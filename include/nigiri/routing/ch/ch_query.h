#pragma once

#include <cstdint>
#include "nigiri/routing/ch/ch_data.h"
#include "nigiri/routing/query.h"
#include "nigiri/types.h"

namespace nigiri {
struct timetable;
}  // namespace nigiri

namespace nigiri::routing {

void obtain_relevant_stops(timetable const& tt,
                           routing::query const& q,
                           profile_idx_t const prf_idx,
                           bitvec& relevant_stops);

struct unpack_label {
  friend bool operator>(unpack_label const& a, unpack_label const& b) {
    return a.l_ > b.l_;
  }
  std::uint32_t l_;
  ch_edge_idx_t e_;
};

struct unpack_get_bucket {
  std::uint32_t operator()(unpack_label const& l) const { return l.l_; }
};

struct unpack_container {
  std::uint16_t child_max_dur_;
  bool child_max_;
  bool child_end_;
  std::vector<tooth> child_max_dur_saw_;
  std::vector<tooth> total_max_dur_saw_;
  std::vector<tooth> left_;
  std::vector<tooth> right_;
  interval<std::int16_t> departure_;
  interval<std::int16_t> arrival_;
};

}  // namespace nigiri::routing
