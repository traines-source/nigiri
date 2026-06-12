#include "utl/helpers/algorithm.h"
#include "utl/insert_sorted.h"
#include "utl/pairwise.h"
#include "utl/verify.h"
#include "utl/zip.h"

#include <cstdint>
#include "nigiri/loader/build_lb_graph.h"
#include "nigiri/common/dial.h"
#include "nigiri/for_each_meta.h"
#include "nigiri/logging.h"
#include "nigiri/routing/ch/ch_data.h"
#include "nigiri/routing/ch/ch_query.h"
#include "nigiri/routing/ch/saw.h"
#include "nigiri/routing/limits.h"
#include "nigiri/td_footpath.h"

#include "nigiri/timetable.h"
#include "nigiri/types.h"
#include <algorithm>
#include <limits>
#include <queue>
#include <vector>

namespace nigiri::routing {

static constexpr auto const kChMaxAdditionalTransfers = kMaxTransfers;  // TODO
static constexpr auto const kToothUnpackMode = false;
static constexpr auto const kDirectUnpackMode = false;
// static constexpr auto const kReconstructMode = true;

void obtain_relevant_stops(timetable const& tt,
                           routing::query const& q,
                           profile_idx_t const prf_idx,
                           bitvec& relevant_stops) {

  auto marked_stations = 0;
  vector_map<ch_edge_idx_t, std::vector<tooth>> edge_min;
  vector_map<ch_edge_idx_t, std::vector<tooth>> edge_max;
  vector_map<ch_edge_idx_t, timetable::ch_edge> graph_edges;
  auto const tmp_edge_offset = tt.ch_graph_max_[prf_idx].size();

  if (tt.fwd_search_ch_graph_[prf_idx].size() != tt.n_locations()) {
    std::cout << "no ch for profile, skipping" << std::endl;
    relevant_stops.one_out();
    return;
  }

  std::cout << "upsearch" << std::endl;

  if (kChSawType == saw_type::kTrafficDaysPower) {
    auto bf = bitvec{};
    bf.resize(tt.ch_traffic_days_[prf_idx].size());
    for (auto const e : tt.ch_graph_min_[prf_idx]) {
      for (auto const& t : e) {
        if (t.traffic_days_ != bitfield_idx_t::invalid()) {

          bf.set(t.traffic_days_.v_);
        }
      }
    }
    std::cout << bf.count() << "/" << bf.size() << std::endl;
    for (auto const e : tt.ch_graph_max_[prf_idx]) {
      for (auto const& t : e) {
        if (t.traffic_days_ != bitfield_idx_t::invalid()) {
          bf.set(t.traffic_days_.v_);
        }
      }
    }
    std::cout << bf.count() << "/" << bf.size() << std::endl;
  }

  std::array<vector_map<location_idx_t, ch_edge_idx_t>, 2> dists;
  dists[0].resize(tt.n_locations());
  dists[1].resize(tt.n_locations());
  auto nonce_map = vector_map<location_idx_t, std::uint32_t>{};
  nonce_map.resize(tt.n_locations());

  auto pq = dial<ch_label, ch_get_bucket>{
      (loader::kEnableDgp ? kDistanceGroups + 1U
                          : tt.n_locations())};
  auto ch_traffic_days =
      traffic_days{tt.ch_traffic_days_[prf_idx], {}};  // TODO avoid copy

  auto const distance_group = [&](location_idx_t const l) {
    if constexpr (!loader::kEnableDgp) {
      utl::fail("using distance_group without kEnableDgp");
    }
    for (auto i = static_cast<std::uint16_t>(0U); i < kDistanceGroups - 1U;
         ++i) {
      if (tt.ch_levels_[prf_idx].at(l) < tt.ch_distance_groups_[prf_idx][i]) {
        return i;
      }
    }
    return static_cast<std::uint16_t>(kDistanceGroups - 1U);
  };

  auto const mark_relevant_stop = [&](location_idx_t const parent) {
    if (loader::kChGroupParents && !relevant_stops.test(parent.v_)) {
      ++marked_stations;
      for (auto const& c : tt.locations_.children_[parent]) {
        relevant_stops.set(c.v_);
        for (auto const& cc : tt.locations_.children_[c]) {
          relevant_stops.set(cc.v_);
        }
      }
    }
    relevant_stops.set(parent.v_);
  };

  auto new_max_dist = std::vector<tooth>{};
  auto new_min_dist = std::vector<tooth>{};
  auto tmp_saw = std::vector<tooth>{};
  // auto mode = kMin;

  auto const min_max_dist_idx = ch_edge_idx_t{edge_max.size()};
  graph_edges.push_back({location_idx_t{0U}, location_idx_t{1U}});
  edge_max.push_back({});
  edge_min.push_back({});
  auto min_max_dist = std::vector<tooth>{};
  auto min_min_dist = std::vector<tooth>{};
  auto meetpoints = hash_set<location_idx_t>{};  // TODO other way of dedup?
  auto counter = 0;

  auto const mark_mp = [&](location_idx_t const l, unsigned const l_dir) {
    auto const other_dir = l_dir ^ 1U;

    if (dists[other_dir][l] != ch_edge_idx_t::invalid() &&
        !edge_max.at(dists[other_dir][l]).empty()) {
      auto max_concat =
          saw<kChSawType>{edge_max.at(dists[l_dir].at(l)), ch_traffic_days}
              .concat(l_dir,
                      saw<kChSawType>{edge_max.at(dists[other_dir][l]),
                                      ch_traffic_days},
                      dists[l_dir].at(l) + tmp_edge_offset,
                      dists[other_dir][l] + tmp_edge_offset, true, tmp_saw);
      max_concat.simplify(saw<kChSawType>{min_max_dist, ch_traffic_days}, true,
                          new_max_dist);
      if (saw<kChSawType>{new_max_dist, ch_traffic_days} !=
          saw<kChSawType>{min_max_dist, ch_traffic_days}) {
        std::swap(min_max_dist, new_max_dist);
        meetpoints.emplace(l);
      } else if (tmp_saw.clear();

                 saw<kChSawType>{edge_min.at(dists[l_dir].at(l)),
                                 ch_traffic_days}
                     .concat(l_dir,
                             saw<kChSawType>{edge_min.at(dists[other_dir][l]),
                                             ch_traffic_days},
                             ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(),
                             false, tmp_saw) <=
                 saw<kChSawType>{min_max_dist, ch_traffic_days}) {
        meetpoints.emplace(l);
      }
      std::cout << "mp found "
                << tt.get_default_translation(tt.locations_.names_.at(l)) << " "
                << saw<kChSawType>{min_max_dist, ch_traffic_days}.max()
                << std::endl;

      new_max_dist.clear();
      tmp_saw.clear();
    }
  };

  auto const follow_edges = [&](location_idx_t const l, unsigned const l_dir,
                                u16_minutes const const_dist) {
    auto const other_dir = l_dir ^ 1U;
    auto const& graph = l_dir == kForward ? tt.fwd_search_ch_graph_[prf_idx]
                                          : tt.bwd_search_ch_graph_[prf_idx];

    // std::cout << "weird" << graph.at(l).size() << std::endl;
    for (auto const& e_idx : graph.at(l)) {
      auto const e = tt.ch_graph_edges_[prf_idx].at(e_idx);
      auto const edge_target = l_dir == kForward ? e.to_ : e.from_;
      // std::cout << "const_dist1" << const_dist << std::endl;
      if (tt.ch_levels_[prf_idx].at(l) >
          tt.ch_levels_[prf_idx].at(edge_target)) {
        continue;
      }
      auto const l_e_idx = dists[l_dir].at(l);

      if (const_dist != u16_minutes::max()) {
        // TODO dead code (?)
        std::cout << "const_dist2" << const_dist << std::endl;
        auto const d = owning_saw<saw_type::kConstant>{
            saw<saw_type::kConstant>::of(const_dist), {}};

        saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(e_idx), ch_traffic_days}
            .concat_const(other_dir, d.to_saw(ch_traffic_days),
                          ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(),
                          new_max_dist);

        saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx), ch_traffic_days}
            .concat_const(other_dir, d.to_saw(ch_traffic_days),
                          ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(),
                          new_min_dist);
      } else {
        saw<kChSawType>{edge_max.at(l_e_idx), ch_traffic_days}.concat(
            l_dir,
            saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(e_idx),
                            ch_traffic_days},
            l_e_idx + tmp_edge_offset, e_idx, true, new_max_dist);

        saw<kChSawType>{edge_min.at(l_e_idx), ch_traffic_days}.concat(
            l_dir,
            saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx),
                            ch_traffic_days},
            l_e_idx + tmp_edge_offset, e_idx, false, new_min_dist);
      }
      // std::cout << "tar" << edge_target << " " << new_max_dist << " ld " <<
      //  l.d_[kMax] << " em " << e.max_dur_.count() << " " << new_min_dist <<
      //  std::endl;

      /*auto const max_true = saw<kChSawType>{new_max_dist,
      ch_traffic_days}.leq(
          dists[l_dir].at(edge_target).d_[kMax].to_saw(ch_traffic_days), true);
      auto const min_true = saw<kChSawType>{new_min_dist, ch_traffic_days}.leq(
          dists[l_dir].at(edge_target).d_[kMin].to_saw(ch_traffic_days), true);
      if (max_true || min_true) {*/
      if (dists[l_dir][edge_target] == 0U) {
        dists[l_dir][edge_target] = ch_edge_idx_t{edge_max.size()};
        graph_edges.push_back({graph_edges.at(l_e_idx).from_, edge_target});
        edge_max.push_back({});
        edge_min.push_back({});
      }

      saw<kChSawType>{new_max_dist, ch_traffic_days}.simplify(
          saw<kChSawType>{edge_max.at(dists[l_dir][edge_target]),
                          ch_traffic_days},
          true,
          tmp_saw);  // TODO move to leq again? or detect within simplify if not
      // equal (new bitfields created etc)
      /*std::cout << "push pq" << edge_target << " " << 0 << " " << 0
                << " new: " << saw<kChSawType>{new_max_dist, ch_traffic_days}
                << std::endl
                << " edge max: "
                << saw<kChSawType>{edge_max.at(dists[l_dir][edge_target]),
                                   ch_traffic_days}
                << std::endl
                << "simpl:" << saw<kChSawType>{tmp_saw, ch_traffic_days}
                << std::endl;*/
      auto max_leq = false;
      auto min_leq = false;
      if (saw<kChSawType>{edge_max.at(dists[l_dir].at(edge_target)),
                          ch_traffic_days} !=
          saw<kChSawType>{tmp_saw, ch_traffic_days}) {
        std::swap(edge_max.at(dists[l_dir].at(edge_target)), tmp_saw);
        max_leq = true;
      }
      new_max_dist.clear();
      tmp_saw.clear();
      saw<kChSawType>{new_min_dist, ch_traffic_days}.simplify(
          saw<kChSawType>{edge_min.at(dists[l_dir].at(edge_target)),
                          ch_traffic_days},
          false, tmp_saw);
      if (saw<kChSawType>{edge_min.at(dists[l_dir].at(edge_target)),
                          ch_traffic_days} !=
          saw<kChSawType>{tmp_saw, ch_traffic_days}) {

        std::swap(edge_min.at(dists[l_dir][edge_target]), tmp_saw);
        min_leq = true;
      }
      new_min_dist.clear();
      tmp_saw.clear();
      if (!min_leq && !max_leq) {
        /*std::cout << "skip " << e.from_ << " " << e.to_ << " " << edge_target
                  << std::endl;*/
        continue;
      }
      mark_mp(edge_target, l_dir);
      if (kEnableDgp && distance_group(l) == distance_group(edge_target)) {
        continue;
      }
      auto const const_max =
          saw<kChSawType>{edge_max.at(dists[l_dir][edge_target]),
                          ch_traffic_days}
              .max();
      auto const const_min =
          saw<kChSawType>{edge_min.at(dists[l_dir][edge_target]),
                          ch_traffic_days}
              .min();
      utl::verify(const_max.count() < kChMaxTravelTime.count() &&
                      const_min.count() < kChMaxTravelTime.count(),
                  "extra weird {} {}", const_max, const_min);
      /*std::cout << "push " << e.from_ << " " << e.to_ << " " << edge_target <<
         " " << tt.get_default_translation(tt.locations_.names_.at(edge_target))
                << " minmay " << const_min << " " << const_max << std::endl;*/

      /*auto const const_min_edge =
          saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx), ch_traffic_days}
              .min();
      if (dist[kMax] + const_min_edge.count() >= kChMaxTravelTime.count()) {

        std::cout << "extra extra weird " << dist[kMax] << " "
                  << const_min_edge.count() << std::endl;

        throw utl::fail("extra extra weird");
      }*/
      pq.push(ch_label{
          edge_target,
          kEnableDgp ? distance_group(edge_target)
                      : tt.ch_levels_[prf_idx].at(edge_target),
          static_cast<std::uint8_t>(l_dir)});
      //}
    }
  };

  for (auto i = location_idx_t{0U}; i < tt.n_locations(); ++i) {
    std::cout << i << " "
              << tt.get_default_translation(tt.locations_.names_.at(i))
              << " l:" << tt.ch_levels_[prf_idx].at(i) << std::endl;
  }

  auto const init = [&](std::vector<routing::offset> offsets,
                        std::uint8_t dir) {
    for (auto const& start : offsets) {  // TODO correct offsets
      for_each_meta(
          tt, dir == kForward ? q.start_match_mode_ : q.dest_match_mode_,
          start.target_, [&](location_idx_t const x) {
            dists[dir].at(x) = ch_edge_idx_t{edge_min.size()};
            graph_edges.push_back({location_idx_t{dir}, x});
            edge_max.push_back(saw<saw_type::kConstant>::of(start.duration()));
            edge_min.push_back(saw<saw_type::kConstant>::of(start.duration()));
            mark_mp(x, dir);
            // mark_relevant_stop(x);  // TODO fix
            pq.push(
                ch_label{x,
                  kEnableDgp ? distance_group(x)
                  : tt.ch_levels_[prf_idx].at(x),
                         dir});
            std::cout << "input" << x << " " << start.duration() << " "
                      << (dir == kForward ? "fw " : "bw ")
                      << tt.get_default_translation(tt.locations_.names_.at(x))
                      << " t:" << relevant_stops.test(x.v_) << std::endl;
          });
    }
  };

  init(q.start_, kForward);
  init(q.destination_, kReverse);

  while (!pq.empty()) {
    ++counter;
    auto l = pq.top();
    pq.pop();
    auto const l_dir = l.dir_ % kModeOffset;
    auto const other_dir = l_dir ^ 1U;

    if (l.level_ <= nonce_map.at(l.l_)) {
      //
      continue;  // TODO
    }
    nonce_map.at(l.l_) = l.level_;

    /*if (dists[l_dir].at(l.l_).d_[kMax].to_saw(ch_traffic_days).max().count() <
            l.d_[kMax] &&  // TODO extrema
        dists[l_dir].at(l.l_).d_[kMin].to_saw(ch_traffic_days).min().count() <
            l.d_[kMin]) {  // TODO nonce?
      continue;
    }*/
    std::cout << "steop " << l.l_ << " "
              << tt.get_default_translation(tt.locations_.names_.at(l.l_))
              << " other:"
              << saw<kChSawType>{edge_max.at(dists[other_dir][l.l_]),
                                 ch_traffic_days}
                     .max()
              << " " << l_dir << " l:" << tt.ch_levels_[prf_idx].at(l.l_)
              << std::endl;
    /*std::cout << "max " << dists[l_dir][l.l_].d_[kMax].to_saw(ch_traffic_days)
              << std::endl;
    std::cout << "max " << dists[l_dir][l.l_].d_[kMin].to_saw(ch_traffic_days)
              << std::endl;*/
    // mark_mp(l.l_, l_dir);
    //  std::cout << "mmd" << min_max_dist << std::endl;
    if (saw<kChSawType>{edge_min.at(dists[l_dir].at(l.l_)), ch_traffic_days}.min() >
        saw<kChSawType>{min_max_dist, ch_traffic_days}.max()) {
      /*if (mode == kMax) {
        auto buffer = std::vector<ch_label>{};
        while (!pq.empty()) {
          auto b = pq.top();
          //b.dir_ += kModeOffset;
          b.d_[kMax] =
      dists[l_dir].at(l.l_).d_[kMin].to_saw(ch_traffic_days).min().count();
          buffer.emplace_back(b);
          pq.pop();
        }
        l.dir_ += kModeOffset;
        pq.push(l);
        for (auto const& b : buffer) {
          pq.push(b);
        }
        std::cout << "switching to min mode " << counter << " "
                  << "minmax: "
                  << saw<kChSawType>{min_max_dist, ch_traffic_days}.max()
                  << " infty: " << std::numeric_limits<ch_label::dist_t>::max()
                  << std::endl;
        mode = kMin;
        continue;
      } else {
        std::cout << "reached ḿax with min " << counter << std::endl;
        break;
      }*/
      // TODO reinstate early stopping
      std::cout << "reached ḿax with min " << counter << std::endl;
      continue;
    }

    //    std::cout << "follow " << mode << l.l_ << std::endl;
    follow_edges(l.l_, l_dir, u16_minutes::max());
  }
  pq.clear();

  auto const invert = [&](std::uint32_t l) {
    return tt.n_locations()-l;
  };

  for (auto const m : meetpoints) {
    saw<kChSawType>{edge_min.at(dists[kForward][m]), ch_traffic_days}.concat(
        saw<kChSawType>{edge_min.at(dists[kReverse][m]), ch_traffic_days},
        ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), false, tmp_saw);
    std::cout << "mp filter " << m << " "
              << tt.get_default_translation(tt.locations_.names_.at(m)) << " "
              << saw<kChSawType>{tmp_saw, ch_traffic_days}.min() << " "
              << saw<kChSawType>{min_min_dist, ch_traffic_days}.min() << " "
              << saw<kChSawType>{min_max_dist, ch_traffic_days}.max()
              << std::endl;
    saw<kChSawType>{tmp_saw, ch_traffic_days}.simplify(
        saw<kChSawType>{min_min_dist, ch_traffic_days}, false, new_min_dist);
    std::swap(min_min_dist, new_min_dist);
    new_min_dist.clear();
    if (saw<kChSawType>{tmp_saw, ch_traffic_days} >
            saw<kChSawType>{min_max_dist, ch_traffic_days} ||
        saw<kChSawType>{tmp_saw, ch_traffic_days}.min() >
            saw<kChSawType>{min_max_dist, ch_traffic_days}
                .max()) {  // TODO werid
      tmp_saw.clear();
      continue;
    }

    std::cout << "taken" << std::endl;
    std::cout << "concat " << saw<kChSawType>{tmp_saw, ch_traffic_days}
              << std::endl;
    std::cout << "min_max" << saw<kChSawType>{min_max_dist, ch_traffic_days}
              << std::endl;
    std::cout << "min_min" << saw<kChSawType>{min_min_dist, ch_traffic_days}
              << std::endl;

    tmp_saw.clear();
    for (auto const dir : {kForward, kReverse}) {
      auto const other_dir = dir ^ 1U;

      saw<kChSawType>{min_max_dist, ch_traffic_days}.concat_const(
          dir,
          saw<saw_type::kConstant>{
              saw<saw_type::kConstant>::of(saw<kChSawType>{
                  edge_min.at(dists[other_dir][m]), ch_traffic_days}
                                               .min()),
              ch_traffic_days},
          ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), new_max_dist,
          true);
      saw<kChSawType>{new_max_dist, ch_traffic_days}.simplify(
          saw<kChSawType>{edge_max.at(dists[dir][m]), ch_traffic_days}, true,
          tmp_saw);
      // std::swap(edge_max.at(dists[dir][m]), tmp_saw);
   
      tmp_saw.clear();
      new_max_dist.clear();
      pq.push(ch_label{m,
       invert(kEnableDgp ? kDistanceGroups : tt.ch_levels_[prf_idx].at(m)),
                       static_cast<std::uint8_t>(dir)});
      std::cout << "added mp " << m << std::endl;
    }
  }

  auto const start_mam = static_cast<std::int16_t>(
      (std::visit(utl::overloaded{
                      [](interval<unixtime_t> const start_interval) {
                        return start_interval.from_;
                      },
                      [](unixtime_t const start_time) { return start_time; }},
                  q.start_time_)
           .time_since_epoch() %
       1440)
          .count());
  auto const min_max_saw = saw<kChSawType>{min_max_dist, ch_traffic_days};
  auto i = 0U;
  auto rit = min_max_saw.end();
  auto const not_const = !min_max_dist.empty() && !min_max_saw.is_constant();
  if (not_const) {
    for (--rit;; --rit) {
      if (rit->mam_ >= start_mam || rit.day_offset_ > 0) {
        ++i;
        if (i >= q.min_connection_count_) {  // TODO searchWindow?
          break;
        }
      }
    }
  }

  auto const minmax_departure = interval{
      static_cast<std::int16_t>(start_mam),
      static_cast<std::int16_t>(not_const ? rit->mam_ + rit.day_offset_ * 1440
                                          : start_mam)};  // TODO arriveBy, utc?

  auto const get_mam_interval = [&](interval<std::int16_t> intvl) {
    if (intvl.size() >= 1440) {
      return interval{static_cast<std::int16_t>(0),
                      static_cast<std::int16_t>(1440)};
    }
    if (intvl.size() <= 0) {
      return interval{static_cast<std::int16_t>(0),
                      static_cast<std::int16_t>(0)};
    }
    return interval{
        static_cast<std::int16_t>((intvl.from_ % 1440 + 1440) % 1440),
        static_cast<std::int16_t>((intvl.to_ % 1440 + 1440) % 1440)};
  };

  std::cout << minmax_departure << " weird" << std::endl;
  if (minmax_departure.size() > 1440) {
    relevant_stops.one_out();
    std::cout << "24h filter, skipping ch" << std::endl;
    // return;
  }

  auto const minmax_departure_mam = get_mam_interval(minmax_departure);
  auto const minmax_arrival =
      interval{saw<kChSawType>{min_min_dist, ch_traffic_days}.arrival(
                   minmax_departure.from_),
               min_max_saw.arrival(minmax_departure.to_)};
  auto const min_number_transfers =
      min_max_dist.size() < kSawMetadataOffset
          ? 0
          : min_max_dist[kSawFieldMin].traffic_days_.v_;
  // auto const const_min_max_dist =
  // static_cast<int>(min_max_saw.max().count());
  edge_max.at(min_max_dist_idx) = min_max_dist;  // TODO avoid copy
  std::cout << "downsearch " << counter << " " << meetpoints.size()
            << std::endl;

  auto queue = dial<unpack_label, unpack_get_bucket>{tt.n_locations()};
  auto unpacking_map = hash_map<ch_edge_idx_t, unpack_container>{};

  auto const pinch_intervals = [&](ch_edge_idx_t const edge_idx, interval<std::int16_t>& left,
    interval<std::int16_t>& right) {
    auto const left_via_e = interval{
        saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(edge_idx), ch_traffic_days}
            .departure(right.from_),
        saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(edge_idx), ch_traffic_days}
            .departure(right.to_)};
    auto const right_via_e = interval{
        saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(edge_idx), ch_traffic_days}
            .arrival(left.from_),
        saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(edge_idx), ch_traffic_days}
            .arrival(left.to_)};
    left = left.intersect(left_via_e);
    right = right.intersect(right_via_e);
  };

  auto const queue_upsert = [&](ch_edge_idx_t e, std::uint16_t child_max_dur,
                                std::uint16_t, std::vector<tooth> const& left,
                                std::vector<tooth> const& right,
                                interval<std::int16_t> const left_intvl,
                                interval<std::int16_t> const right_intvl) {
    auto unpacking_e = unpacking_map.find(e);
    if (unpacking_e != unpacking_map.end()) {
      // TODO check min > max, filter
      saw<kChSawType>{left, ch_traffic_days}.simplify(
          saw<kChSawType>{unpacking_e->second.left_, ch_traffic_days}, true,
          tmp_saw);
      std::swap(unpacking_e->second.left_, tmp_saw);
      tmp_saw.clear();
      saw<kChSawType>{right, ch_traffic_days}.simplify(
          saw<kChSawType>{unpacking_e->second.right_, ch_traffic_days}, true,
          tmp_saw);
      std::swap(unpacking_e->second.right_, tmp_saw);
      unpacking_e->second.child_max_dur_ =
          std::max(unpacking_e->second.child_max_dur_, child_max_dur);
      tmp_saw.clear();
      unpacking_e->second.departure_ =
          unpacking_e->second.departure_.connect(left_intvl);
      unpacking_e->second.arrival_ =
          unpacking_e->second.arrival_.connect(right_intvl);
    } else {
      unpacking_map.emplace_hint(
          unpacking_e,
          std::pair{e,
                    unpack_container{
                        .child_max_dur_ = child_max_dur,
                        .child_max_ = false,
                        .child_end_ = false,
                        .child_max_dur_saw_ = {}, /*std::move(arr_max_saw)*/
                        .total_max_dur_saw_ = {}, /*std::move(pushdown_left)*/
                        .left_ = std::move(left),
                        .right_ = std::move(right),
                        .departure_ = left_intvl,
                        .arrival_ = right_intvl}});
      auto const& ee = tt.ch_graph_edges_[prf_idx].at(e);
      queue.push(unpack_label{
          tt.n_locations() - std::min(tt.ch_levels_[prf_idx].at(ee.from_),
                                      tt.ch_levels_[prf_idx].at(ee.to_)),
          e});
    }
  };

  auto const unpack_children = [&](int) {
    auto unpacked_transfers = 0;
    auto unpacked_minmax = 0;
    auto unpacked_arr = 0;
    auto unpacked_dep = 0;
    auto unpacked_pinch = 0;
    auto unpacked_push = 0;

    while (!queue.empty()) {
      auto [level, child_edge_idx] = queue.top();
      auto const c = unpacking_map.at(child_edge_idx);  // TODO avoid copy
      /*std::cout << "stack " << child_edge_idx << " cmd: " << child_max_dur
                << std::endl;*/

      queue.pop();
      /*if (!kToothUnpackMode &&
          visited.at(child_edge_idx) >=
              c.child_max_dur_) {  // TODO use pq ordered by child_max_dur?
        unpacking_map.erase(child_edge_idx);
        continue;
      }
      visited[child_edge_idx] = c.child_max_dur_;*/

      // std::cout << "unp: invlvl:" << level << " " << child_edge_idx << " " <<
      // unpacking_map.size() <<  std::endl;

      if (kToothUnpackMode) {
        /*
        auto const tooth_idx = child_max_dur;  // TODO cleanup

        std::cout << "tooth" << tooth_idx << std::endl;

        auto const tooth =
            child_max ? (child_edge_idx >= tmp_edge_offset
                             ? edge_max.at(child_edge_idx - tmp_edge_offset)
                                   .at(tooth_idx)
                             : tt.ch_graph_max_[prf_idx]
                                   .at(child_edge_idx)
                                   .at(tooth_idx))
                      : (child_edge_idx >= tmp_edge_offset
                             ? edge_min.at(child_edge_idx - tmp_edge_offset)
                                   .at(tooth_idx)
                             : tt.ch_graph_min_[prf_idx]
                                   .at(child_edge_idx)
                                   .at(tooth_idx));  // TODO avoid copy
        auto const& parent_edge =
            child_edge_idx >= tmp_edge_offset
                ? graph_edges.at(child_edge_idx - tmp_edge_offset)
                : tt.ch_graph_edges_[prf_idx].at(child_edge_idx);

        std::cout << "ft ldmax" << l_d_max << " " << parent_edge.from_
                  << " l:" << tt.ch_levels_[prf_idx].at(parent_edge.from_)
                  << " "
                  << tt.get_default_translation(
                         tt.locations_.names_.at(parent_edge.from_))
                  << " -> " << parent_edge.to_
                  << " l:" << tt.ch_levels_[prf_idx].at(parent_edge.to_) << " "
                  << tt.get_default_translation(
                         tt.locations_.names_.at(parent_edge.to_))
                  << std::endl;

        if (tooth.start_ != ch_edge_idx_t::invalid()) {
          auto const& start_edge =
              tooth.start_ >= tmp_edge_offset
                  ? graph_edges.at(tooth.start_ - tmp_edge_offset)
                  : tt.ch_graph_edges_[prf_idx].at(tooth.start_);

          mark_relevant_stop(start_edge.to_);
          std::cout << " transfer a " << start_edge.to_
                    << " l:" << tt.ch_levels_[prf_idx].at(start_edge.to_) << " "
                    << tt.get_default_translation(
                           tt.locations_.names_.at(start_edge.to_))
                    << std::endl;

          std::cout << "stack push a" << tooth.start_ << " " << tooth.start_idx_
                    << std::endl;
          queue.push({tooth.start_,
                      tooth.start_idx_,
                      child_max,
                      false,
                      {},
                      {},
                      {},
                      {}});
        }
        if (tooth.end_ != ch_edge_idx_t::invalid()) {
          auto const& end_edge =  // TODO might be invalid?
              tooth.end_ >= tmp_edge_offset
                  ? graph_edges.at(tooth.end_ - tmp_edge_offset)
                  : tt.ch_graph_edges_[prf_idx].at(tooth.end_);

          if (tooth.start_ == ch_edge_idx_t::invalid()) {
            mark_relevant_stop(end_edge.from_);
          }
          std::cout << " transfer b " << end_edge.from_
                    << " l:" << tt.ch_levels_[prf_idx].at(end_edge.from_) << " "
                    << tt.get_default_translation(
                           tt.locations_.names_.at(end_edge.from_))
                    << std::endl;
          std::cout << "stack push b" << " " << tooth.end_ << " "
                    << tooth.end_idx_ << std::endl;

          queue.push(
              {tooth.end_, tooth.end_idx_, child_max, true, {}, {}, {}, {}});
        }
        */
      } else {
        for (auto const [unpack, transfer] :
             utl::zip(tt.ch_graph_unpack_[prf_idx].at(child_edge_idx),
                      tt.ch_graph_transfers_[prf_idx].at(child_edge_idx))) {
          if (unpack.second == ch_edge_idx_t::invalid()) {
            if (transfer != location_idx_t::invalid()) {
              mark_relevant_stop(transfer);
            }
            continue;
          }
          auto const arr_min_saw = saw<kChSawType>{
              tt.ch_graph_min_[prf_idx].at(unpack.first), ch_traffic_days};
          auto const dep_min_saw = saw<kChSawType>{
              tt.ch_graph_min_[prf_idx].at(unpack.second), ch_traffic_days};
          auto const arr_min = arr_min_saw.min();
          auto const dep_min = dep_min_saw.min();

          auto left_next = std::vector<tooth>{};  // TODO alloc
          auto right_next = std::vector<tooth>{};

          saw<kChSawType>{c.left_, ch_traffic_days}.concat(
              kForward, arr_min_saw, ch_edge_idx_t::invalid(),
              ch_edge_idx_t::invalid(), false, left_next);

          saw<kChSawType>{c.right_, ch_traffic_days}.concat(
              kReverse, dep_min_saw, ch_edge_idx_t::invalid(),
              ch_edge_idx_t::invalid(), false, right_next);

          saw<kChSawType>{left_next, ch_traffic_days}.concat(
              kForward, saw<kChSawType>{right_next, ch_traffic_days},
              ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), false,
              new_min_dist);

          unpacked_transfers++;
          if (new_min_dist.empty() ||
              new_min_dist[kSawFieldMin].traffic_days_ >
                  std::min(kMaxTransfers + 0U,
                           min_number_transfers + kChMaxAdditionalTransfers)) {
            // std::cout << "skip pushdown l due transfers" << std::endl;
            tmp_saw.clear();
            new_min_dist.clear();
            continue;
          }

          unpacked_minmax++;

          if (min_max_saw.less(saw<kChSawType>{new_min_dist, ch_traffic_days},
                               false, minmax_departure_mam)) {
            // std::cout << "skip pushdown l" << std::endl;
            tmp_saw.clear();
            new_min_dist.clear();
            continue;
          }

          tmp_saw.clear();
          new_min_dist.clear();

          auto arr_max_saw = std::vector<tooth>{};  // TODO alloc
          auto dep_max_saw = std::vector<tooth>{};

          saw<kChSawType>{
              tt.ch_graph_max_[prf_idx].at(child_edge_idx),  // TODO pushdown
              ch_traffic_days}
              .concat_const(
                  kForward,
                  saw<saw_type::kConstant>{
                      saw<saw_type::kConstant>::of(dep_min), ch_traffic_days},
                  ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), tmp_saw,
                  true);
          saw<kChSawType>{tmp_saw, ch_traffic_days}.simplify(
              saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(unpack.first),
                              ch_traffic_days},
              true, arr_max_saw);
          tmp_saw.clear();

          auto const arrival_left = get_mam_interval(interval{
              saw<kChSawType>{c.left_, ch_traffic_days}.arrival(
                  minmax_departure.from_),
              arr_min_saw.departure(
                  (saw<kChSawType>{right_next, ch_traffic_days}.departure(
                      minmax_arrival.to_)))});

          auto const arrival_left_next = get_mam_interval(
              interval{saw<kChSawType>{left_next, ch_traffic_days}.arrival(
                           minmax_departure.from_),
                       saw<kChSawType>{right_next, ch_traffic_days}.departure(
                           minmax_arrival.to_)});  // TODO min/max bounds?

          if (arrival_left.size() == 0 ||
              arrival_left_next.size() == 0) {  // TODO exclusive to?
            // std::cout << "skip due interval" << std::endl;
            continue;
          }

          if (unpacked_arr % 1000 == 0) {
            std::cout << "filter: dep:" << minmax_departure << " "
                      << "mam:" << minmax_departure_mam
                      << " arr:" << minmax_arrival << " "
                      << "segmentdep: left: " << arrival_left
                      << " next:" << arrival_left_next
                      << " min_max: " << min_max_saw.max() << " min_min: "
                      << saw<kChSawType>{min_min_dist, ch_traffic_days}.min()
                      << left_next.size() << " " << right_next.size() << " "
                      << c.left_.size() << " " << c.right_.size() << "intvls: " << c.departure_ << " " << c.arrival_ << std::endl;
          }

          // TODO min/max bounds?

          unpacked_arr++;
          if (saw<kChSawType>{arr_max_saw, ch_traffic_days}.less(
                  arr_min_saw, false, arrival_left)) {
            // std::cout << "skip" << std::endl;
            continue;  // TODO count occurs
          }

          saw<kChSawType>{
              tt.ch_graph_max_[prf_idx].at(child_edge_idx),  // TODO pushdown
              ch_traffic_days}
              .concat_const(
                  kReverse,
                  saw<saw_type::kConstant>{
                      saw<saw_type::kConstant>::of(arr_min), ch_traffic_days},
                  ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), tmp_saw,
                  true);  // TODO is this correct in conjunction with filter?
          saw<kChSawType>{tmp_saw, ch_traffic_days}.simplify(
              saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(unpack.second),
                              ch_traffic_days},
              true, dep_max_saw);
          tmp_saw.clear();

          unpacked_dep++;
          if (saw<kChSawType>{dep_max_saw, ch_traffic_days}.less(
                  dep_min_saw, false, arrival_left_next)) {
            // std::cout << "skip" << std::endl;
            continue;  // TODO count occurs
          }
          if (transfer != location_idx_t::invalid()) {
            /*std::cout << "ft ldmax" << l_d_max << " "
                      << tt.get_default_translation(tt.locations_.names_.at(
                             tt.ch_graph_edges_[prf_idx][child_edge_idx].from_))
                      << " -> "
                      << tt.get_default_translation(tt.locations_.names_.at(
                             tt.ch_graph_edges_[prf_idx][child_edge_idx].to_))
                      << " transfer "
                      << tt.get_default_translation(
                             tt.locations_.names_.at(transfer))
                      << " arr: " << arr_min << " "
                      << saw<kChSawType>{arr_max_saw, ch_traffic_days}.max()
                      << " "
                      << " dep: " << dep_min << " "
                      << saw<kChSawType>{dep_max_saw, ch_traffic_days}.max()
                      << std::endl;*/
          }

          if (transfer != location_idx_t::invalid()) {
            mark_relevant_stop(transfer);
          }

          unpacked_pinch++;

          auto left_intvl = c.departure_;
          auto right_intvl = c.arrival_;
          auto center_intvl = interval{static_cast<std::int16_t>(0), std::numeric_limits<std::int16_t>::max()};
          pinch_intervals(unpack.first, left_intvl, center_intvl);
          pinch_intervals(unpack.second, center_intvl, right_intvl);
          pinch_intervals(unpack.first, left_intvl, center_intvl);

          if (left_intvl.empty() || right_intvl.empty() || center_intvl.empty()) {
            continue;
          }

          unpacked_push++;

          queue_upsert(
              unpack.first,
              saw<kChSawType>{arr_max_saw, ch_traffic_days}.max().count(),
              arr_min.count(), c.left_, std::move(right_next), left_intvl, center_intvl);
          queue_upsert(
              unpack.second,
              saw<kChSawType>{dep_max_saw, ch_traffic_days}.max().count(),
              dep_min.count(), std::move(left_next), c.right_, center_intvl, right_intvl);

          /*std::cout << "stack push " << unpack.first << " " <<
             unpack.second
                    << " qs:" << queue.size() << std::endl;*/
        }
      }
      unpacking_map.erase(child_edge_idx);
    }

    std::cout << "unpacked: " << unpacked_push
              << "/"
                 " transfers:"
              << unpacked_transfers << " minmax:" << unpacked_minmax
              << " arr:" << unpacked_arr << " dep:" << unpacked_dep << " pinch:" << unpacked_pinch
              << " push:" << unpacked_push << " "
              << tt.ch_graph_edges_[prf_idx].size() << std::endl;
    new_max_dist.clear();
  };

  if constexpr (kDirectUnpackMode) {
    /*utl::verify(kToothUnpackMode, "needs kToothUnpackMode");
    auto const s = saw<kChSawType>{min_max_dist, ch_traffic_days};
    for (auto it = s.begin(); it != s.end(); ++it) {
      std::cout << "min max dist idx " << min_max_dist_idx + tmp_edge_offset
                << " " << it.pos_ << std::endl;
      queue.push({min_max_dist_idx + tmp_edge_offset,
                  static_cast<std::uint16_t>(it.pos_),
                  true,
                  false,
                  {},
                  {},
                  {},
                  {},
                  {},
                  {}});
    }
    unpack_children(const_min_max_dist);
    std::cout << "directly marked stops: " << relevant_stops.count() << "/"
              << relevant_stops.size() << std::endl;
    std::cout << "bitfields: " << "/" << ch_traffic_days.bitfields_.size()
              << std::endl;
    return;*/
  }

  nonce_map.clear();
  nonce_map.resize(tt.n_locations());

  while (!pq.empty()) {
    auto l = pq.top();
    auto const other_dir = l.dir_ ^ 1U;
    pq.pop();

    if (l.level_ <= nonce_map.at(l.l_)) {
      continue;
    }
    /*std::cout << "xxdown " << l.l_ << " "
              << tt.get_default_translation(tt.locations_.names_.at(l.l_))
              // << " min: " << dists[l.dir_][l.l_].d_[kMin] << " "
              << " max: " << l_d_max << " nonce: " << l.d_[kMin]
              << " dir:" << (l.dir_ == kForward ? "fwd" : "bwd")
              << "| l:" << tt.ch_levels_[prf_idx].at(l.l_) << std::endl;*/
    nonce_map.at(l.l_) = l.level_;

    tmp_saw.clear();
    new_max_dist.clear();
    new_min_dist.clear();

    auto edge_max_dist = std::vector<tooth>{};  // TODO alloc
    saw<kChSawType>{min_max_dist, ch_traffic_days}.concat_const(
        l.dir_,
        saw<saw_type::kConstant>{
            saw<saw_type::kConstant>::of(saw<kChSawType>{
                edge_min.at(dists[other_dir][l.l_]), ch_traffic_days}
                                             .min()),
            ch_traffic_days},
        ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), tmp_saw, true);

    saw<kChSawType>{tmp_saw, ch_traffic_days}.simplify(
        saw<kChSawType>{edge_max.at(dists[l.dir_][l.l_]), ch_traffic_days},
        true, edge_max_dist);

    tmp_saw.clear();

    saw<kChSawType>{edge_max.at(dists[l.dir_][l.l_]), ch_traffic_days}.concat(
        l.dir_,
        saw<kChSawType>{edge_max.at(dists[other_dir][l.l_]), ch_traffic_days},
        ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), true,
        tmp_saw);  // TODO is this correctly updated/revisted?

    saw<kChSawType>{tmp_saw, ch_traffic_days}.simplify(
        saw<kChSawType>{min_max_dist, ch_traffic_days}, true, new_max_dist);
    /*if (saw<kChSawType>{tmp_saw, ch_traffic_days} ==
        dists[l.dir_][l.l_].d_[kMax].to_saw(
            ch_traffic_days)) {  // TODO improve leq pre-pq-push?
      mark_relevant_stop(l.l_);
      tmp_saw.clear();
      continue;
    }*/
    /*std::swap(edge_max.at(dists[l.dir_][l.l_]),
              tmp_saw); */  // TODO min with l_d_max-e.min_dur
    tmp_saw.clear();
    mark_relevant_stop(l.l_);
    auto const& graph = l.dir_ == kReverse ? tt.fwd_search_ch_graph_[prf_idx]
                                           : tt.bwd_search_ch_graph_[prf_idx];

    auto followed_edges = 0;
    auto mindist_edges = 0;
    auto interval_edges = 0;
    auto transfer_edges = 0;
    auto mindistviaprev_edges = 0;
    auto prevlabel_edges = 0;
    auto level_edges = 0;
    for (auto const& e_idx : graph[l.l_]) {
      // std::cout << "edge" << e_idx << std::endl;
      auto const e = tt.ch_graph_edges_[prf_idx][e_idx];
      auto const edge_target = l.dir_ == kReverse ? e.to_ : e.from_;
      ++level_edges;

      /*std::cout << "down edge " << edge_target << " "
              <<
         tt.get_default_translation(tt.locations_.names_.at(edge_target))
              // << " min: " << dists[l.dir_][l.l_].d_[kMin] << " "
              << " max: " << l_d_max << " nonce: " << l.d_[kMin]
              << " dir:" << (l.dir_ == kForward ? "fwd" : "bwd")
              << "| l:" << tt.ch_levels_[prf_idx].at(edge_target) << std::endl;
              std::cout << "followed edges: " << followed_edges
              << "/"
                 " mindist:"
              << mindist_edges << " interval:" << interval_edges
              << " mindistviaprev:" << mindistviaprev_edges
              << " transfer:" << transfer_edges
              << " prevlabel:" << prevlabel_edges << " level:" << level_edges
              << " total:" << graph[l.l_].size() << std::endl;
              tmp_saw.clear();*/

      if (tt.ch_levels_[prf_idx][l.l_] < tt.ch_levels_[prf_idx][edge_target]) {
        continue;
      }
      /*if (kEnableDgp && l_d_max == distance_group(edge_target)) {
        continue;
      }*/
      auto const& prev_label = dists[l.dir_][edge_target];
      ++prevlabel_edges;

      if (prev_label == ch_edge_idx_t::invalid()) {
        continue;
      }

      saw<kChSawType>{edge_min.at(prev_label), ch_traffic_days}.concat(
          l.dir_,
          saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx), ch_traffic_days},
          ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), false, tmp_saw);
      auto min_dist_via_prev = saw<kChSawType>{tmp_saw, ch_traffic_days};
      // auto min_dist_via_prev_const = min_dist_via_prev.min().count();

      min_dist_via_prev.concat(
          l.dir_,
          saw<kChSawType>{edge_min.at(dists[other_dir][l.l_]), ch_traffic_days},
          ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), false,
          new_min_dist);

      ++transfer_edges;

      if (new_min_dist.empty() ||
          (new_min_dist.size() >
               kSawMetadataOffset &&  // TODO cleanup const saws
           new_min_dist[kSawFieldMin].traffic_days_ >
               std::min(kMaxTransfers + 0U,
                        min_number_transfers + kChMaxAdditionalTransfers))) {
        if (!new_min_dist.empty()) {
          std::cout << "skip pushdown l due transfers"
                    << new_min_dist[kSawFieldMin].traffic_days_ << " "
                    << std::min(
                           kMaxTransfers + 0U,
                           min_number_transfers + kChMaxAdditionalTransfers)
                    << std::endl;
        }
        tmp_saw.clear();
        new_min_dist.clear();
        continue;
      }

      ++mindistviaprev_edges;

      // TODO l_d_max cheat, stopping criterion, cutoff?
      if (/*min_dist_via_prev_const > l_d_max ||*/
          !min_dist_via_prev.leq(
              saw<kChSawType>{edge_max_dist, ch_traffic_days},
              false) ||  // TODO filter
          saw<kChSawType>{new_max_dist, ch_traffic_days}.less(
              saw<kChSawType>{new_min_dist, ch_traffic_days}, false,
              minmax_departure_mam)) {  // TODO exact_true correct?
        tmp_saw.clear();
        new_min_dist.clear();
        continue;
      }
      // std::cout << saw<kChSawType>{new_min_dist, ch_traffic_days} <<
      // std::endl;

      /*std::cout << "down edge " << l_d_max << " "
                << tt.get_default_translation(tt.locations_.names_.at(
                       tt.ch_graph_edges_[prf_idx][e_idx].from_))
                << " -> "
                << tt.get_default_translation(tt.locations_.names_.at(
                       tt.ch_graph_edges_[prf_idx][e_idx].to_))
                << std::endl;*/

      /*if (min_dist_via_prev.max().count() >=
          kChMaxTravelTime.count()) {  // TODO expensive
        std::cout << "weird" << min_dist_via_prev.max().count() << " "
                  << l_d_max << " " << std::endl;
        tmp_saw.clear();
        continue;
      }*/

      // TODO move to pq pop?

      if (kToothUnpackMode) {
        /*auto max = false;
        for (auto const& saw :
             {saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx),
                              ch_traffic_days},
              saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(e_idx),
                              ch_traffic_days}}) {
          for (auto it = saw.begin(); it != saw.end(); ++it) {
            queue.push({e_idx,
                        static_cast<std::uint16_t>(it.pos_),
                        max,
                        false,
                        {},
                        {},
                        {},
                        {},
                        {},
                        {}});
          }
          max = true;
        }*/
      } else {

        /*auto const arrival_x =
            l.dir_ == kForward
                ? interval{saw<kChSawType>{edge_min.at(prev_label),
                                           ch_traffic_days}
                               .arrival(minmax_departure.from_),
                           std::min(
                               minmax_arrival.to_,
                               saw<kChSawType>{
                                   tt.ch_graph_min_[prf_idx].at(e_idx),
                                   ch_traffic_days}
                                   .departure(
                                       (saw<kChSawType>{edge_max_dist,
                                                        ch_traffic_days}
                                            .arrival(minmax_departure.to_))))}
                : interval{
                      std::max(minmax_departure.from_,
                               saw<kChSawType>{edge_min.at(dists[l.dir_][l.l_]),
                                               ch_traffic_days}
                                   .departure(minmax_arrival.from_)),
                      min_dist_via_prev.departure(minmax_arrival.to_)}; // TODO
        buffer overflow???

        auto const arrival = get_mam_interval(arrival_x);*/

        tmp_saw.clear();
        new_min_dist.clear();

        auto pushdown_edge_max_dist = std::vector<tooth>{};
        saw<kChSawType>{edge_max_dist, ch_traffic_days}.concat_const(
            other_dir,
            saw<saw_type::kConstant>{
                saw<saw_type::kConstant>::of(
                    saw<kChSawType>{edge_min.at(prev_label), ch_traffic_days}
                        .min()),
                ch_traffic_days},
            ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), new_min_dist,
            true);
        saw<kChSawType>{new_min_dist, ch_traffic_days}.simplify(
            saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(e_idx),
                            ch_traffic_days},
            true, pushdown_edge_max_dist);

        new_min_dist.clear();

        auto pushdown_max_dist = std::vector<tooth>{};

        saw<kChSawType>{edge_min.at(prev_label), ch_traffic_days}
            .concat(l.dir_,
                    saw<kChSawType>{tt.ch_graph_max_[prf_idx].at(e_idx),
                                    ch_traffic_days},
                    ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), true,
                    tmp_saw)
            .concat(l.dir_,
                    saw<kChSawType>{edge_min.at(dists[other_dir][l.l_]),
                                    ch_traffic_days},
                    ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), true,
                    new_min_dist)
            .simplify(saw<kChSawType>{min_max_dist, ch_traffic_days}, true,
                      pushdown_max_dist);

        /*std::cout << "filter: dep:" << minmax_departure << " "
                  << "mam:" << minmax_departure_mam << " arr:" <<
           minmax_arrival
                  << " "
                  << "segmentdep: " << arrival_x << "mam:" << arrival << " "
                  << interval{minmax_departure.from_,

                              (saw<kChSawType>{edge_max_dist,
           ch_traffic_days} .arrival(minmax_departure.to_))}
                  << " "
                  <<
           interval{saw<kChSawType>{edge_min.at(dists[l.dir_][l.l_]),
                                              ch_traffic_days}
                                  .min(),
                              min_dist_via_prev.min()}
                  << " " << (l.dir_ == kForward) << std::endl;*/

        ++interval_edges;

        /*if (arrival.size() == 0) {  // TODO exclusive to?
          // std::cout << "skip due interval" << std::endl;
          tmp_saw.clear();
          new_min_dist.clear();
          continue;
        }*/

        // TODO pop?
        // mark_relevant_stop(edge_target);

        tmp_saw.clear();
        new_min_dist.clear();

        auto const left_idx =
            l.dir_ == kForward ? prev_label : dists[kForward][l.l_];

        auto const right_idx =
            l.dir_ == kForward ? dists[kReverse][l.l_] : prev_label;

        auto left_intvl = interval{
            saw<kChSawType>{edge_min.at(left_idx), ch_traffic_days}.arrival(
                minmax_departure.from_),
            saw<kChSawType>{edge_max.at(left_idx), ch_traffic_days}.arrival(
                minmax_departure.to_)};

        auto right_intvl = interval{
            saw<kChSawType>{edge_max.at(right_idx), ch_traffic_days}.departure(
                minmax_arrival.from_),
            saw<kChSawType>{edge_min.at(right_idx), ch_traffic_days}.departure(
                minmax_arrival.to_)};

        pinch_intervals(e_idx, left_intvl, right_intvl);

        // std::cout << "queue_upsert" << std::endl;
        queue_upsert(e_idx,
                     saw<kChSawType>{pushdown_edge_max_dist, ch_traffic_days}
                         .max()
                         .count(),
                     saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx),
                                     ch_traffic_days}
                         .min()
                         .count(),
                     edge_min.at(left_idx),  // TODO avoid copy
                     edge_min.at(right_idx), left_intvl, right_intvl);

        /*queue.push({e_idx,
                    static_cast<ch_label::dist_t>(
                        saw<kChSawType>{pushdown_edge_max_dist, ch_traffic_days}
                            .max()
                            .count()),
                    false, false, pushdown_edge_max_dist,
                    std::move(pushdown_edge_max_dist),
                    saw<saw_type::kConstant>::of(duration_t{0U}),
                    saw<saw_type::kConstant>::of(duration_t{0U}), arrival,
                    std::move(pushdown_max_dist)});*/
        /*std::move(pushdown_max_dist), // appears to be slightly worse
        l.dir_ == kReverse ? edge_min.at(dists[other_dir][l.l_])
                           : edge_min.at(prev_label),
        l.dir_ == kForward ? edge_min.at(dists[other_dir][l.l_])
                           : edge_min.at(prev_label)});*/
        tmp_saw.clear();
        new_min_dist.clear();
      }

      if (dists[other_dir][edge_target] == 0U) {
        dists[other_dir][edge_target] = ch_edge_idx_t{edge_max.size()};
        graph_edges.push_back(
            {location_idx_t::invalid(), location_idx_t::invalid()});
        edge_max.push_back({});
        edge_min.push_back({});
      }
      saw<kChSawType>{edge_min.at(dists[other_dir][l.l_]), ch_traffic_days}
          .concat(other_dir,
                  saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx),
                                  ch_traffic_days},
                  ch_edge_idx_t::invalid(), ch_edge_idx_t::invalid(), false,
                  tmp_saw);
      saw<kChSawType>{tmp_saw, ch_traffic_days}.simplify(
          saw<kChSawType>{edge_min.at(dists[other_dir][edge_target]),
                          ch_traffic_days},
          false, new_min_dist);

      ++mindist_edges;

      if (saw<kChSawType>{new_min_dist, ch_traffic_days} ==
          saw<kChSawType>{edge_min.at(dists[other_dir][edge_target]),
                          ch_traffic_days}) {
        tmp_saw.clear();
        new_min_dist.clear();
        continue;
      }
      std::swap(edge_min.at(dists[other_dir][edge_target]), new_min_dist);
      tmp_saw.clear();
      new_min_dist.clear();

      auto const x = saw<kChSawType>{tt.ch_graph_min_[prf_idx].at(e_idx),
                                     ch_traffic_days}  // TODO deconcat?
                         .min();
      utl::verify(x != u16_minutes::max(), "min is infty");
      /*std::cout << "diff " << x << " ld " << l_d_max << " em "
                << saw<kChSawType>{edge_max.at(dists[l.dir_][edge_target]),
                                   ch_traffic_days}
                       .max()
                       .count()
                << std::endl;*/

      // std::cout << "pq_push" << std::endl;
      pq.push(ch_label{
          edge_target,
          invert(kEnableDgp
                      ? distance_group(edge_target)
                      : tt.ch_levels_[prf_idx].at(edge_target)),
          static_cast<std::uint8_t>(l.dir_)});

      tmp_saw.clear();
      ++followed_edges;
    }
    std::cout << "followed edges: " << followed_edges
              << "/"
                 " mindist:"
              << mindist_edges << " interval:" << interval_edges
              << " mindistviaprev:" << mindistviaprev_edges
              << " transfer:" << transfer_edges
              << " prevlabel:" << prevlabel_edges << " level:" << level_edges
              << " total:" << graph[l.l_].size() << std::endl;
    tmp_saw.clear();
    new_max_dist.clear();
  }

  std::cout << "unp: size: " << unpacking_map.size() << std::endl;

  unpack_children(0);
  // relevant_stops.one_out();
  /*relevant_stops.zero_out();
  for (auto l : {66733, 66707,
    66707, 14037,
    14037, 24022,
    24022, 44946,
    44946, 60390,
    66733, 66707,
    66707, 14037,
    14037, 17360,
    17360, 17346,
    17346, 23630,
    23630, 23631,
    23631, 24051,
    24051, 45331,
    45331, 60392,
    66731, 67390,
    67390, 67386,
    67386, 66705,
    66705, 14037,
    14037, 24022,
    24022, 44946,
    44946, 60390,
    66731, 67390,
    67390, 67386,
    67386, 66705,
    66705, 14037,
    14037, 17360,
    17360, 17346,
    17346, 23630,
    23630, 23631,
    23631, 24051,
    24051, 45331,
    45331, 60392,
    66733, 66707,
    66707, 14038,
    14038, 24022,
    24022, 44946,
    44946, 60390,
    66733, 66707,
    66707, 14038,
    14038, 17360,
    17360, 17370,
    17370, 23630,
    23630, 23631,
    23631, 24051,
    24051, 45331,
    45331, 60392}) {
    relevant_stops.set(static_cast<unsigned>(l));
  }*/
  init(q.start_, kForward);
  init(q.destination_, kReverse);
  std::cout << "marked stops: " << relevant_stops.count() << "/"
            << relevant_stops.size() << std::endl;
  std::cout << "marked stations: " << marked_stations << std::endl;
  std::cout << "bitfields: " << "/" << ch_traffic_days.bitfields_.size()
            << std::endl;
}
}  // namespace nigiri::routing