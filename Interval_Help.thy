theory Interval_Help
  imports "HOL-Library.Interval" "HOL-Decision_Procs.Approximation_Bounds"

begin

section "General Lemmas on Intervals"

definition Interval'' where
"Interval'' = (\<lambda>(l,u). if (l :: 'a :: linorder) \<le> u then Interval (l, u) else Interval (u, l))"

lemma normal_interval'': "l \<le> u \<Longrightarrow> Interval'' (l, u) = Interval (l, u)" unfolding Interval''_def by simp

definition closed_real_segment :: "real \<Rightarrow> real \<Rightarrow> real set" where
"closed_real_segment a b = (if a \<le> b then {a..b} else {b..a})"

lemma lower_Interval[simp]: "l \<le> u \<Longrightarrow> lower (Interval (l, u)) = l"
by (metis Ivl.rep_eq bounds_of_interval_inverse fst_conv lower.rep_eq min_def)

lemma upper_Interval[simp]: "l \<le> u \<Longrightarrow> upper (Interval (l, u)) = u"
by (simp add: Interval_inverse upper.rep_eq)

lemma set_of_Interval: "l \<le> u \<Longrightarrow> set_of (Interval (l, u)) = {l..u}"
  by (simp add: set_of_eq)

lemma sign_of_element: "upper ivl < 0 \<Longrightarrow> \<forall>x \<in> set_of ivl. x < 0"
  by (metis atLeastAtMost_iff le_less_trans set_of_eq)

lemma sign_of_element': "0 < lower ivl \<Longrightarrow> \<forall>x \<in> set_of ivl. 0 < x"
  by (simp add: less_le_trans set_of_eq)

section "Lemmas and Definitions on Real Intervals"
subsection "General"

(* inverse, iff 0 \<notin> ivl, this is guaranteed in the implementation *)
definition inverse_interval' :: "real interval \<Rightarrow> real interval" where
"inverse_interval' ivl = Interval (inverse (upper ivl), inverse (lower ivl))"

lemma inverse_in_inverse_interval': "x \<in> set_of ivl \<and> 0 \<notin> set_of ivl \<Longrightarrow> inverse x \<in> set_of (inverse_interval' ivl)"
  by (smt atLeastAtMost_iff inverse_interval'_def le_imp_inverse_le le_imp_inverse_le_neg lower_Interval set_of_eq upper_Interval)

fun set_of_interval_list:: "real interval list \<Rightarrow> real set" where
"set_of_interval_list (ivl#ivls) = set_of ivl \<union> set_of_interval_list ivls" |
"set_of_interval_list [] = {}"

lemma in_interval_in_set_of_interval_list: "x \<in> set_of ivl \<Longrightarrow> x \<in> set_of_interval_list (ivls @ ivl # ivls')"
  by (induct ivls) auto

lemma in_larger_interval_list_set_l: "x \<in> set_of_interval_list ivls \<Longrightarrow> x \<in> set_of_interval_list (ivls' @ ivls)"
  by (induct ivls') auto

lemma in_larger_interval_list_set_r: "x \<in> set_of_interval_list ivls \<Longrightarrow> x \<in> set_of_interval_list (ivls @ ivls')"
  by (induct ivls) auto

subsection "Intersections and Split"

(* ivl \<inter> ivl' *)
definition interval_intersection:: "real interval \<Rightarrow> real interval \<Rightarrow> real interval list" where
"interval_intersection ivl ivl' = (
  if upper ivl' < lower ivl \<or> upper ivl < lower ivl' then []
  else [Interval (max (lower ivl) (lower ivl'), min (upper ivl) (upper ivl'))]
)"

(* x \<in> ivl \<and> x \<in> ivl' \<Longrightarrow> ivl \<inter> ivl' *)
lemma in_both_intervals_in_intersection:
  assumes "x \<in> set_of ivl" "x \<in> set_of ivl'"
  shows "x \<in> set_of_interval_list (interval_intersection ivl ivl')"
proof -
  have order: "lower ivl \<le> x \<and> x \<le> upper ivl \<and> lower ivl' \<le> x \<and> x \<le> upper ivl'" using assms(1) assms(2) by (simp add: set_of_eq)
  then have "x \<in> set_of (Interval (max (lower ivl) (lower ivl'), min (upper ivl) (upper ivl')))" by (simp add: set_of_eq)
  then show ?thesis using in_interval_in_set_of_interval_list interval_intersection_def order by auto
qed

(* ivl \<inter> [l,\<infinity>) *)
definition interval_intersection_unbounded_upper:: "real interval \<Rightarrow> real \<Rightarrow> real interval list" where
"interval_intersection_unbounded_upper ivl l = (
  if upper ivl < l then []
  else [Interval (max (lower ivl) l, upper ivl)]
)"

(* x \<in> ivl \<and> x \<in> [l,\<infinity>) \<Longrightarrow> ivl \<inter> [l,\<infinity>) *)
lemma in_both_intervals_in_uu_intersection:
  assumes "x \<in> set_of ivl" "l \<le> x"
  shows "x \<in> set_of_interval_list (interval_intersection_unbounded_upper ivl l)"
proof -
  have "lower ivl \<le> x \<and> x \<le> upper ivl" using assms(1) by (simp add: set_of_eq)
  then have "max (lower ivl) l \<le> x \<and> x \<le> upper ivl" by (simp add: assms(2))
  then show ?thesis using interval_intersection_unbounded_upper_def by (simp add: set_of_eq)
qed

(* (\<infinity>,u] \<inter> ivl *)
definition interval_intersection_unbounded_lower:: "real interval \<Rightarrow> real \<Rightarrow> real interval list" where
"interval_intersection_unbounded_lower ivl u = (
  if u < lower ivl then []
  else [Interval (lower ivl, min (upper ivl) u)]
)"

(* x \<in> (\<infinity>,u] \<and> x \<in> ivl \<Longrightarrow> (\<infinity>,u] \<inter> ivl *)
lemma in_both_intervals_in_ul_intersection:
  assumes "x \<in> set_of ivl" "x \<le> u"
  shows "x \<in> set_of_interval_list (interval_intersection_unbounded_lower ivl u)"
proof -
  have "lower ivl \<le> x \<and> x \<le> upper ivl" using assms(1) by (simp add: set_of_eq)
  then have "lower ivl \<le> x \<and> x \<le> min (upper ivl) u" by (simp add: assms(2))
  then show ?thesis using interval_intersection_unbounded_lower_def by (simp add: set_of_eq)
qed

(* m \<in> [l,u] \<Longrightarrow> [l,u] \<leadsto> [l,m],[m,u] *)
definition split_interval:: "real interval \<Rightarrow> real \<Rightarrow> real interval list" where
"split_interval ivl m = (if m \<in> set_of ivl then [Interval (lower ivl, m), Interval (m, upper ivl)] else [ivl])"

(* m \<in> [l,u] \<Longrightarrow> [l,u] = [l,m] \<union> [m,u] *)
lemma split_same_set: "set_of ivl = set_of_interval_list (split_interval ivl m)"
proof (cases "m \<in> set_of ivl")
case True
  show ?thesis
  proof
    show "set_of ivl \<subseteq> set_of_interval_list (split_interval ivl m)"
    proof
      fix x
      assume x: "x \<in> set_of ivl"
      then have "lower ivl \<le> x \<and> x \<le> upper ivl \<and> m \<le> x \<or> x \<le> m" by (auto simp: set_of_eq)
      then have "lower ivl \<le> x \<and> x \<le> m \<or> m \<le> x \<and> x \<le> upper ivl" using set_of_eq x by fastforce 
      then show "x \<in> set_of_interval_list (split_interval ivl m)" using True split_interval_def by (simp add: set_of_eq)
    qed
  next
    show "set_of_interval_list (split_interval ivl m) \<subseteq> set_of ivl"
    proof
      fix x
      assume "x \<in> set_of_interval_list (split_interval ivl m)"
      then have "lower ivl \<le> x \<and> x \<le> m \<or> m \<le> x \<and> x \<le> upper ivl" using True split_interval_def by (simp add: set_of_eq)
      then have "lower ivl \<le> x \<and> x \<le> upper ivl" using True atLeastAtMost_iff by (auto simp: set_of_eq)
      then show "x \<in> set_of ivl" by (simp add: set_of_eq)
    qed
  qed
next
  case False
  then show ?thesis using split_interval_def by simp
qed

section "Lemmas and Definitions on Float Intervals"
subsection "General"

(* inverse, iff 0 \<notin> ivl; inverse_float_interval without option *)
definition inverse_float_interval':: "nat \<Rightarrow> float interval \<Rightarrow> float interval" where
"inverse_float_interval' prec ivl = Interval'' (float_divl prec 1 (upper ivl), float_divr prec 1 (lower ivl))"

fun set_of_float_interval_list:: "float interval list \<Rightarrow> float set" where
"set_of_float_interval_list (ivl#ivls) = set_of ivl \<union> set_of_float_interval_list ivls" |
"set_of_float_interval_list [] = {}"

lemma in_float_interval_in_set_of_float_interval_list: "x \<in> set_of ivl \<Longrightarrow> x \<in> set_of_float_interval_list (ivls @ ivl # ivls')"
  by (induct ivls) auto

lemma in_larger_float_interval_list_set_l: "x \<in> set_of_float_interval_list ivls \<Longrightarrow> x \<in> set_of_float_interval_list (ivls' @ ivls)"
  by (induct ivls') auto

lemma in_larger_float_interval_list_set_r: "x \<in> set_of_float_interval_list ivls \<Longrightarrow> x \<in> set_of_float_interval_list (ivls @ ivls')"
  by (induct ivls) auto

lemma in_float_interval_list_in_set_of_float_interval:
  "x \<in> set_of_float_interval_list ivls \<Longrightarrow> \<exists>i. x \<in> set_of (ivls ! i) \<and> i < length ivls"
proof (induction ivls)
  case Nil
  then show ?case by simp
next
  case (Cons ivl ivls)
  then show ?case
  proof (cases "x \<in> set_of ivl")
    case True
    then have "x \<in> set_of ((ivl # ivls) ! 0) \<and> 0 < length (ivl # ivls)" by simp
    then show ?thesis by blast
  next
    case False
    then obtain i where i: "x \<in> set_of (ivls ! i)" "i < length ivls"  using Cons.IH Cons.prems by auto
    then have "x \<in> set_of ((ivl # ivls) ! (i + 1)) \<and> (i + 1) < length (ivl # ivls)" by auto
    then show ?thesis by blast 
  qed
qed

fun real_set_of_float_interval_list:: "float interval list \<Rightarrow> real set" where
"real_set_of_float_interval_list (ivl#ivls) = set_of (real_interval ivl) \<union> real_set_of_float_interval_list ivls" |
"real_set_of_float_interval_list [] = {}"

lemma in_float_interval_in_real_set_of_float_interval_list: "x \<in> set_of (real_interval ivl) \<Longrightarrow> x \<in> real_set_of_float_interval_list (ivls @ ivl # ivls')"
  by (induct ivls) auto

lemma in_larger_real_set_of_float_interval_list_l: "x \<in> real_set_of_float_interval_list ivls \<Longrightarrow> x \<in> real_set_of_float_interval_list (ivls' @ ivls)"
  by (induct ivls') auto

lemma in_larger_real_set_of_float_interval_list_r: "x \<in> real_set_of_float_interval_list ivls \<Longrightarrow> x \<in> real_set_of_float_interval_list (ivls @ ivls')"
  by (induct ivls) auto

lemma in_float_interval_list_in_set_of_float_interval':
  "x \<in> real_set_of_float_interval_list ivls \<Longrightarrow> \<exists>i. x \<in> set_of (real_interval (ivls ! i)) \<and> i < length ivls"
proof (induction ivls)
  case Nil
  then show ?case by simp
next
  case (Cons ivl ivls)
  thm Cons.IH
  then show ?case
  proof (cases "x \<in> set_of (real_interval ivl)")
    case True
    then have "x \<in> set_of (real_interval ((ivl # ivls) ! 0)) \<and> 0 < length (ivl # ivls)" by simp
    then show ?thesis by blast
  next
    case False
    then obtain i where i: "x \<in> set_of (real_interval (ivls ! i))" "i < length ivls"  using Cons.IH Cons.prems by auto
    then have "x \<in> set_of (real_interval ((ivl # ivls) ! (i + 1))) \<and> (i + 1) < length (ivl # ivls)" by auto
    then show ?thesis by blast
  qed
qed

lemma in_rounded_interval_list:
  "x \<in> real_set_of_float_interval_list ivls \<Longrightarrow> x \<in> real_set_of_float_interval_list (map (round_interval prec) ivls)"
  by (induct ivls) (auto simp: in_round_intervalI)

lemma real_interval_subset:
  assumes "ivl \<le> ivl'"
  shows "real_interval ivl \<le> real_interval ivl'"
proof -
  have "lower ivl' \<le> lower ivl \<and> upper ivl \<le> upper ivl'" using assms using less_eq_interval_def by blast
  then show ?thesis by (simp add: less_eq_interval_def) 
qed

subsection "Definition of plus_float_interval"

context includes interval.lifting

begin

lift_definition plus_float_interval::"nat \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>prec. \<lambda>(a1, a2). \<lambda>(b1, b2). (float_plus_down prec a1 b1, float_plus_up prec a2 b2)"
  by (auto intro!: add_mono simp: float_plus_down_le float_plus_up_le)

lemma lower_plus_float_interval:
  "lower (plus_float_interval prec ivl ivl') = float_plus_down prec (lower ivl) (lower ivl')"
  by transfer auto
lemma upper_plus_float_interval:
  "upper (plus_float_interval prec ivl ivl') = float_plus_up prec (upper ivl) (upper ivl')"
  by transfer auto

lemma plus_float_interval_monotonic:
  "set_of (ivl + ivl') \<subseteq> set_of (plus_float_interval prec ivl ivl')"
  using float_plus_down_le float_plus_up_le lower_plus_float_interval upper_plus_float_interval
  by (simp add: set_of_subset_iff)

lemma plus_float_interval:
  "set_of (real_interval A) + set_of (real_interval B) \<subseteq>
    set_of (real_interval (plus_float_interval prec A B))"
proof
  fix x
  assume x: "x \<in> set_of (real_interval A) + set_of (real_interval B)"
  then have x: "x \<in> set_of(real_interval (A + B))" by (metis plus_in_float_intervalI set_plus_elim) 
  then have "lower A + lower B \<le> x \<and> x \<le> upper A + upper B" by (simp add: set_of_eq)
  then have "float_plus_down prec (lower A) (lower B) \<le> x \<and> x \<le> float_plus_up prec (upper A) (upper B)"
    by (simp add: float_plus_down_le float_plus_up_le)
  then show "x \<in> set_of (real_interval (plus_float_interval prec A B))"
    by (simp add: in_intervalI lower_plus_float_interval upper_plus_float_interval) 
qed

lemma plus_float_interval_mono:
  assumes "a \<le> real_interval a'" "b \<le> real_interval b'"
  shows   "a + b \<le> real_interval (plus_float_interval prec a' b')"
  using assms float_plus_down float_plus_up lower_plus_float_interval upper_plus_float_interval
  by (smt (z3) less_eq_interval_def lower_plus lower_real_interval upper_plus upper_real_interval)

lemma minus_float_interval_monotonic:
  "set_of (ivl - ivl') \<subseteq> set_of (plus_float_interval prec ivl (- ivl'))"
  using float_plus_down_le float_plus_up_le lower_plus_float_interval upper_plus_float_interval
  by (simp add: minus_interval_def plus_float_interval_monotonic)

end

subsection "Intersections and Split"

(* ivl \<inter> ivl' *)
definition float_interval_intersection:: "float interval \<Rightarrow> float interval \<Rightarrow> float interval list" where
"float_interval_intersection ivl ivl' = (
  if upper ivl' < lower ivl \<or> upper ivl < lower ivl' then []
  else [Interval (max (lower ivl) (lower ivl'), min (upper ivl) (upper ivl'))]
)"

(* x \<in> ivl \<and> x \<in> ivl' \<Longrightarrow> x \<in> ivl \<inter> ivl' *)
lemma in_both_float_intervals_in_float_intersection:
  assumes "x \<in> set_of ivl" "x \<in> set_of ivl'"
  shows "x \<in> set_of_float_interval_list (float_interval_intersection ivl ivl')"
proof -
  have order: "lower ivl \<le> x \<and> x \<le> upper ivl \<and> lower ivl' \<le> x \<and> x \<le> upper ivl'" using assms(1) assms(2) by (simp add: set_of_eq)
  then have "x \<in> set_of (Interval (max (lower ivl) (lower ivl'), min (upper ivl) (upper ivl')))"
    by (metis atLeastAtMost_iff max.bounded_iff min.bounded_iff order.trans set_of_Interval) 
  then show ?thesis using order by (simp add: float_interval_intersection_def)
qed

lemma in_both_float_intervals_in_float_intersection':
  assumes "x \<in> set_of (real_interval ivl)" "x \<in> set_of (real_interval ivl')"
  shows "x \<in> real_set_of_float_interval_list (float_interval_intersection ivl ivl')"
proof -
  have order: "lower ivl \<le> x \<and> x \<le> upper ivl \<and> lower ivl' \<le> x \<and> x \<le> upper ivl'" using assms(1) assms(2) by (simp add: set_of_eq)
  then have "x \<in> set_of (real_interval (Interval (max (lower ivl) (lower ivl'), min (upper ivl) (upper ivl'))))"
    using in_real_intervalI by auto
  then show ?thesis using order by (simp add: float_interval_intersection_def)
qed

(* ivl \<inter> [l,\<infinity>) *)
definition float_interval_intersection_unbounded_upper:: "float interval \<Rightarrow> float \<Rightarrow> float interval list" where
"float_interval_intersection_unbounded_upper ivl l = (
  if upper ivl < l then []
  else [Interval (max (lower ivl) l, upper ivl)]
)"

(* x \<in> ivl \<and> x \<in> [l,\<infinity>) \<Longrightarrow> ivl \<inter> [l,\<infinity>) *)
lemma in_both_float_intervals_in_uu_intersection:
  assumes "x \<in> set_of ivl" "l \<le> x"
  shows "x \<in> set_of_float_interval_list (float_interval_intersection_unbounded_upper ivl l)"
proof -
  have "lower ivl \<le> x \<and> x \<le> upper ivl" using assms(1) by (simp add: set_of_eq)
  then show ?thesis using float_interval_intersection_unbounded_upper_def assms(2) by (auto simp add: set_of_eq)
qed

lemma in_both_float_intervals_in_uu_intersection':
  assumes "x \<in> set_of (real_interval ivl)" "l \<le> x"
  shows "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_upper ivl l)"
proof -
  have "lower ivl \<le> x \<and> x \<le> upper ivl" using assms(1) by (simp add: set_of_eq)
  then show ?thesis using float_interval_intersection_unbounded_upper_def assms(2) by (auto simp: set_of_eq)
qed

(* (\<infinity>,u] \<inter> ivl *)
definition float_interval_intersection_unbounded_lower:: "float interval \<Rightarrow> float \<Rightarrow> float interval list" where
"float_interval_intersection_unbounded_lower ivl u = (
  if u < lower ivl then []
  else [Interval (lower ivl, min (upper ivl) u)]
)"

(* x \<in> (\<infinity>,u] \<and> x \<in> ivl \<Longrightarrow> (\<infinity>,u] \<inter> ivl *)
lemma in_both_float_intervals_in_ul_intersection:
  assumes "x \<in> set_of ivl" "x \<le> u"
  shows "x \<in> set_of_float_interval_list (float_interval_intersection_unbounded_lower ivl u)"
proof -
  have "lower ivl \<le> x \<and> x \<le> upper ivl" using assms(1) by (simp add: set_of_eq)
  then show ?thesis using float_interval_intersection_unbounded_lower_def assms(2) by (auto simp add: set_of_eq)
qed

lemma in_both_float_intervals_in_ul_intersection':
  assumes "x \<in> set_of (real_interval ivl)" "x \<le> u"
  shows "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_lower ivl u)"
proof -
  have "lower ivl \<le> x \<and> x \<le> upper ivl" using assms(1) by (simp add: set_of_eq)
  then show ?thesis using float_interval_intersection_unbounded_lower_def assms(2) by (auto simp add: set_of_eq)
qed

(* x \<in> (\<infinity>,u] \<and> x \<in> ivl \<Longrightarrow> (\<infinity>,u] \<inter> ivl *)
definition split_float_interval:: "float interval \<Rightarrow> float \<Rightarrow> float interval list" where
"split_float_interval ivl m = (if m \<in> set_of ivl then [Interval (lower ivl, m), Interval (m, upper ivl)] else [ivl])"

(* x \<in> (\<infinity>,u] \<and> x \<in> ivl \<Longrightarrow> (\<infinity>,u] \<inter> ivl *)
lemma split_float_same_set: "set_of ivl = set_of_float_interval_list (split_float_interval ivl m)"
proof (cases "m \<in> set_of ivl")
case True
  show ?thesis
  proof
    show "set_of ivl \<subseteq> set_of_float_interval_list (split_float_interval ivl m)"
    proof
      fix x
      assume x: "x \<in> set_of ivl"
      then have "lower ivl \<le> x \<and> x \<le> upper ivl \<and> m \<le> x \<or> x \<le> m" by (auto simp: set_of_eq)
      then have "lower ivl \<le> x \<and> x \<le> m \<or> m \<le> x \<and> x \<le> upper ivl" using set_of_eq x atLeastAtMost_iff by blast 
      then show "x \<in> set_of_float_interval_list (split_float_interval ivl m)" using True split_float_interval_def by (simp add: set_of_eq)
    qed
  next
    show "set_of_float_interval_list (split_float_interval ivl m) \<subseteq> set_of ivl"
    proof
      fix x
      assume x: "x \<in> set_of_float_interval_list (split_float_interval ivl m)"
      then have "lower ivl \<le> x \<and> x \<le> m \<or> m \<le> x \<and> x \<le> upper ivl" using True split_float_interval_def by (simp add: set_of_eq)
      then have "lower ivl \<le> x \<and> x \<le> upper ivl" using True atLeastAtMost_iff by (auto simp: set_of_eq)
      then show "x \<in> set_of ivl" by (simp add: set_of_eq)
    qed
  qed
next
  case False
  then show ?thesis using split_float_interval_def by simp
qed

lemma split_float_same_set': "set_of (real_interval ivl) = real_set_of_float_interval_list (split_float_interval ivl m)"
proof (cases "m \<in> set_of ivl")
case True
  show ?thesis
  proof
    show "set_of (real_interval ivl) \<subseteq> real_set_of_float_interval_list (split_float_interval ivl m)"
    proof
      fix x
      assume x: "x \<in> set_of (real_interval ivl)"
      then have "lower ivl \<le> x \<and> x \<le> upper ivl \<and> m \<le> x \<or> x \<le> m" by (auto simp: set_of_eq)
      then have "lower ivl \<le> x \<and> x \<le> m \<or> m \<le> x \<and> x \<le> upper ivl"
        using set_of_eq x atLeastAtMost_iff by (metis lower_real_interval) 
      then show "x \<in> real_set_of_float_interval_list (split_float_interval ivl m)"
        using True split_float_interval_def by (simp add: set_of_eq)
    qed
  next
    show "real_set_of_float_interval_list (split_float_interval ivl m) \<subseteq> set_of (real_interval ivl)"
    proof
      fix x
      assume x: "x \<in> real_set_of_float_interval_list (split_float_interval ivl m)"
      then have "lower ivl \<le> x \<and> x \<le> m \<or> m \<le> x \<and> x \<le> upper ivl"
        using True split_float_interval_def by (simp add: set_of_eq)
      then have "lower ivl \<le> x \<and> x \<le> upper ivl" using True atLeastAtMost_iff by (auto simp: set_of_eq)
      then show "x \<in> set_of (real_interval ivl)" by (simp add: set_of_eq)
    qed
  qed
next
  case False
  then show ?thesis using split_float_interval_def by simp
qed

subsection "Lemmas Showing Monotonicity"

lemma set_of_subset_iff':
  "set_of a \<subseteq> set_of (b :: 'a :: linorder interval) \<longleftrightarrow> a \<le> b"
  unfolding less_eq_interval_def set_of_subset_iff ..

lemma set_of_times': "set_of (a * b) = set_of a * set_of b"
  for a b :: "'a :: {linordered_ring, real_normed_algebra, linear_continuum_topology} interval"
  by (auto simp: set_of_times set_times_def)

lemma mult_mono_interval:
  fixes a b :: "'a :: {linordered_ring, real_normed_algebra, linear_continuum_topology} interval"
  assumes "a \<le> a'" "b \<le> b'"
  shows   "a * b \<le> a' * b'"
  using assms unfolding set_of_subset_iff'[symmetric] set_of_times' by (intro set_times_mono2)

lemma add_mono_interval:
  assumes "a \<le> a'" "b \<le> b'"
  shows   "a + b \<le> a' + (b' :: 'a :: ordered_ab_semigroup_add interval)"
  using assms
  by (auto simp: less_eq_interval_def add_mono)

lemma diff_mono_interval:
  assumes "a \<le> a'" "b \<le> b'"
  shows   "a - b \<le> a' - (b' :: 'a :: ordered_ab_group_add interval)"
  using assms
  by (auto simp: less_eq_interval_def diff_mono)

lemma add_mono_real_interval:
  assumes "a \<le> real_interval a'" "b \<le> real_interval b'"
  shows   "a + b \<le> real_interval (a' + b')"
  using assms
  by (auto simp: less_eq_interval_def add_mono)

lemma diff_mono_real_interval:
  assumes "a \<le> real_interval a'" "b \<le> real_interval b'"
  shows   "a - b \<le> real_interval (a' - b')"
  using assms
  by (auto simp: less_eq_interval_def diff_mono)

lemma mult_float_interval_mono:
  assumes "a \<le> real_interval a'" "b \<le> real_interval b'"
  shows   "a * b \<le> real_interval (mult_float_interval prec a' b')"
proof -
  have "a * b \<le> real_interval a' * real_interval b'"
    by (intro mult_mono_interval assms)
  also {
    have "set_of (real_interval a' * real_interval b') =
            set_of (real_interval a') * set_of (real_interval b')"
      by (auto simp: set_of_times set_times_def)
    also have "\<dots> \<subseteq> set_of (real_interval (mult_float_interval prec a' b'))"
      by (rule mult_float_interval)
    finally have "real_interval a' * real_interval b' \<le> real_interval (mult_float_interval prec a' b')"
      by (simp add: set_of_subset_iff')
  }
  finally show ?thesis .
qed

lemma real_of_float_le_iff: "real_of_float x \<le> real_of_float y \<longleftrightarrow> x \<le> y"
  by simp

lemma real_of_float_less_iff: "real_of_float x < real_of_float y \<longleftrightarrow> x < y"
  by simp

lemma real_of_float_leI: "x \<le> y \<Longrightarrow> real_of_float x \<le> real_of_float y"
  by simp

lemma inverse_float_interval'_correctness:
  assumes "0 \<notin> set_of ivl"
  shows lower_inverse_float_interval:
          "lower (inverse_float_interval' prec ivl) = float_divl prec 1 (upper ivl)"
    and upper_inverse_float_interval:
          "upper (inverse_float_interval' prec ivl) = float_divr prec 1 (lower ivl)"
proof -
  from assms have "lower ivl > 0 \<or> upper ivl < 0"
    by (meson in_intervalI not_le)
  moreover have "real_of_float (lower ivl) \<le> real_of_float (upper ivl)"
    by (meson less_eq_float.rep_eq lower_le_upper)
  ultimately have *: "1 / real_of_float (upper ivl) \<le> 1 / real_of_float (lower ivl)"
    by (auto simp: divide_simps)

  show "lower (inverse_float_interval' prec ivl) = float_divl prec 1 (upper ivl)"
    using *  unfolding inverse_float_interval'_def
    by (smt Interval''_def Interval_Help.lower_Interval float_divl float_divr normal_interval'' one_float.rep_eq real_of_float_le_iff)
  show "upper (inverse_float_interval' prec ivl) = float_divr prec 1 (lower ivl)"
    using * unfolding inverse_float_interval'_def
    by (smt Interval''_def Interval_Help.upper_Interval float_divl float_divr normal_interval'' one_float.rep_eq real_of_float_le_iff)
qed

lemma inverse_interval'_correctness:
  assumes "0 \<notin> set_of ivl"
  shows   lower_inverse_interval': "lower (inverse_interval' ivl) = inverse (upper ivl)"
    and   upper_inverse_interval': "upper (inverse_interval' ivl) = inverse (lower ivl)"
proof -
  have "lower ivl > 0 \<or> upper ivl < 0"
    using assms by (meson in_intervalI not_le)
  hence *: "inverse (upper ivl) \<le> inverse (lower ivl)"
    by (auto simp: divide_simps)
  show "lower (inverse_interval' ivl) = inverse (upper ivl)"
    using * unfolding inverse_interval'_def
    by (subst lower.abs_eq) (auto simp: eq_onp_def)
  show "upper (inverse_interval' ivl) = inverse (lower ivl)"
    using * unfolding inverse_interval'_def
    by (subst upper.abs_eq) (auto simp: eq_onp_def)
qed

lemma inverse_float_interval'_mono:
  assumes "a \<le> real_interval a'" "0 \<notin> set_of a'"
  shows   "inverse_interval' a \<le> real_interval (inverse_float_interval' prec a')"
proof -
  have *: "lower a' > 0 \<or> upper a' < 0"
    using assms(2) by (meson in_intervalI not_le)
  have **: "real_of_float (lower a') \<le> real_of_float (upper a')"
    by (intro real_of_float_leI lower_le_upper)
  have ***: "1 / real_of_float (upper a') \<le> inverse (upper a)"
            "1 / real_of_float (lower a') \<ge> inverse (lower a)"
    using * ** lower_le_upper[of a] assms
      by (auto simp: divide_simps less_eq_interval_def simp del: lower_le_upper)
  have "0 \<notin> set_of a"
    using assms
    by (metis atLeastAtMost_iff in_mono less_eq_float.rep_eq lower_real_interval set_of_eq
              set_of_subset_iff' upper_real_interval zero_float.rep_eq)
  thus ?thesis using assms ***
    by (auto simp: less_eq_interval_def lower_inverse_float_interval upper_inverse_float_interval
                   lower_inverse_interval' upper_inverse_interval'
             intro!: order.trans[OF float_divl] order.trans[OF _ float_divr])
qed

lemma real_interval_interval_of [simp]:
  "real_interval (interval_of m) = interval_of (real_of_float m)"
  by (simp add: interval_eq_iff)

end