theory Interval_Newton_Method
  imports Interval_Help Complex_Main "HOL-Decision_Procs.Approximation" "HOL-Library.Monad_Syntax"
          "HOL-Analysis.Derivative"

begin

section "Preparation of the Proof"

subsection "Lemmas on Derivatives"

lemma mvt_very_simple':
  fixes f :: "real \<Rightarrow> real"
  assumes "l \<le> u"
    and derf: "\<And>x. \<lbrakk>l \<le> x; x \<le> u\<rbrakk> \<Longrightarrow> (f has_field_derivative f' x) (at x within {l..u})"
  shows "\<exists>s \<in> {l..u}. f u - f l = f' s * (u - l)"
  using mvt_very_simple[of l u f "\<lambda>x y. f' x * y"] assms
  by (auto simp: has_field_derivative_def)

lemma deriv_is_zero:
  fixes f :: "real \<Rightarrow> real"
  assumes "l \<le> u"
    and derf: "\<And>x. \<lbrakk>l \<le> x; x \<le> u\<rbrakk> \<Longrightarrow> (f has_field_derivative (\<lambda>x. 0) x) (at x within {l..u})"
  shows "\<forall>x \<in> {l..u}. \<forall>x' \<in> {l..u}. f x = f x'"
  by (metis atLeastAtMost_iff convex_real_interval(5) derf has_field_derivative_zero_constant)

subsection "f(m) is a Value"

locale newton_step_locale = 
  fixes f f' :: "real \<Rightarrow> real"
  fixes X F' :: "real interval"
  fixes m :: real
  assumes f': "x \<in> set_of X \<Longrightarrow> (f has_field_derivative f' x)(at x within set_of X)"
  assumes f'_enclosure: "x \<in> set_of X \<Longrightarrow> f' x \<in> set_of F'"
  assumes m: "m \<in> set_of X"

begin

lemma transfer_field_derivative:
  assumes "c \<in> set_of X" "d \<in> set_of X" "x \<in> {c..d}"
  shows "(f has_field_derivative f' x)(at x within {c..d})"
proof -
  have subset: "{c..d} \<subseteq> set_of X" using assms(1-2) by (simp add: set_of_eq) 
  have "x \<in> set_of X" by (meson assms(1-3) atLeastAtMost_iff connectedD_interval connected_set_of)
  then have "(f has_field_derivative f' x)(at x within set_of X)" using f' by simp
  then show ?thesis using subset has_field_derivative_subset by blast
qed

lemma transfer_mvt: "c \<in> set_of X \<and> d \<in> set_of X \<and> c < d \<Longrightarrow> \<exists>s \<in> {c..d}. f d - f c = f' s * (d - c)"
  using transfer_field_derivative mvt_very_simple' by auto

lemma transfer_enclosure: "c \<in> set_of X \<and> d \<in> set_of X \<Longrightarrow> x \<in> {c..d} \<Longrightarrow> f' x \<in> set_of F'"
  using f'_enclosure by (auto simp add: set_of_eq)

lemma f_transformed:
  assumes "x \<in> set_of X" "y \<in> set_of X" "x < y"
  shows "\<exists>s \<in> {x..y}. f x = f y + f' s * (x - y)"
  using assms by (smt (verit) assms right_diff_distrib' transfer_mvt)

lemma unequal_values:
  assumes "x \<in> set_of X" "y \<in> set_of X" "x < y" "0 \<notin> set_of F'" 
  shows "f x \<noteq> f y"
proof -
  obtain s where s: "s \<in> {x..y} \<and> f y - f x = f' s * (y - x)" using transfer_mvt assms(1-3) by blast
  have "f' s \<noteq> 0" using assms transfer_enclosure s by metis
  then show ?thesis using assms(3) s by auto
qed

lemma f_transformed_with_unequal_values:
  assumes "x \<in> set_of X" "f x = 0" "y \<in> set_of X" "x < y" "f x \<noteq> f y"
  shows "\<exists>s \<in> {x..y}. x = y - f y / f' s"
proof -
  obtain s where s: "s \<in> {x..y} \<and> f x = f y + f' s * (x - y)" and f's_nz: "f' s \<noteq> 0"
    by (metis add.commute add.left_neutral assms f_transformed mult_zero_left)
  then have "f x = f y + f' s * (x - y)" by auto
  then have "f y + f' s * (x - y) = 0" using assms by auto
  then have "f y / f' s + (x - y) = 0"
    using f's_nz by (simp add: add.commute add_num_frac mult.commute)
  then have "x = y - f y / f' s" by auto
  then show ?thesis using s by blast
qed

lemma f_transformed_with_unequal_values':
  assumes "x \<in> set_of X" "f x = 0" "y \<in> set_of X" "y < x" "f x \<noteq> f y"
  shows "\<exists>s \<in> {y..x}. x = y - f y / f' s"
proof -
  obtain s where s: "s \<in> {y..x} \<and> f x = f y + f' s * (x - y)" and f's_nz: "f' s \<noteq> 0"
    using assms(1,3-5) transfer_mvt by force
  then have "f x = f y + f' s * (x - y)" by auto
  then have "f y + f' s * (x - y) = 0" using assms by auto
  then have "f y / f' s + (x - y) = 0"
    using f's_nz by (simp add: add.commute add_num_frac mult.commute)
  then have "x = y - f y / f' s" by auto
  then show ?thesis using s by blast
qed

lemma enclosure_not_zero:
  assumes "x \<in> set_of X" "f x = 0" "0 \<notin> set_of F'"
  shows "x \<in> set_of (interval_of m - interval_of (f m) * inverse_interval' F')"
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume "x < m"
    then obtain s where s: "s \<in> {x..m} \<and> x = m - f m / f' s"
      using f_transformed_with_unequal_values unequal_values assms m by blast
    then have "f' s \<in> set_of F'" using assms(1) m transfer_enclosure by auto
    then have "inverse (f' s) \<in> set_of (inverse_interval' F')"
      by (simp add: assms(3) inverse_in_inverse_interval')
    then have "m - f m / f' s \<in> set_of (interval_of m - interval_of (f m ) * inverse_interval' F')"
      by (simp add: times_in_intervalI field_class.field_divide_inverse minus_in_intervalI
          in_interval_to_interval)
    then show ?thesis by (simp add: s)
  next
    assume "x = m"
    then show ?thesis
      using assms(2) minus_in_intervalI set_of_mul_contains_zero by force 
  next
    assume "x > m"
    then obtain s where s: "s \<in> {m..x} \<and> x = m - f m / f' s"
      using f_transformed_with_unequal_values' unequal_values assms m by metis
    then have "f' s \<in> set_of F'" using assms(1) m transfer_enclosure by auto
    then have "inverse (f' s) \<in> set_of (inverse_interval' F')"
      by (simp add: assms(3) inverse_in_inverse_interval')
    then have "m - f m / f' s \<in> set_of (interval_of m - interval_of (f m) * inverse_interval' F')"
      by (simp add: times_in_intervalI field_class.field_divide_inverse minus_in_intervalI
          in_interval_to_interval)
    then show ?thesis by (simp add: s)
  qed
qed

lemma enclosure_with_upper_zero: (* x \<in> (-\<infinity>, m - f m / \<down>F'] *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> upper F' = 0" "f m < 0"
  shows "x \<le> m - f m / lower F'"
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume l: "x < m"
    then obtain s where s: "s \<in> {x..m}" "x = m - f m / f' s"
      by (metis assms(1,2,4) f_transformed_with_unequal_values m mult_eq_0_iff not_real_square_gt_zero)
    then show ?thesis using set_of_eq
      by (smt (z3) assms(1,4) atLeastAtMost_iff divide_left_mono_neg l m mult_neg_neg
          transfer_enclosure zero_less_divide_iff)
  next
    assume "x = m"
    then show ?thesis using assms(2) by auto 
  next
    assume g: "x > m"
    then obtain s where s: "s \<in> {m..x} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values' m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,3,4) atLeastAtMost_iff divide_nonpos_nonpos g m transfer_enclosure)
  qed
qed

lemma enclosure_with_upper_zero': (* x \<in> [m - f m / \<down>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> upper F' = 0" "f m > 0"
  shows "x \<ge> m - f m / lower F'"
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume l: "x < m"
    then obtain s where s: "s \<in> {x..m} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,3,4) atLeastAtMost_iff divide_nonneg_nonpos l m transfer_enclosure) 
  next
    assume "x = m"
    then show ?thesis using assms(2) by auto 
  next
    assume g: "x > m"
    then obtain s where s: "s \<in> {m..x}" "x = m - f m / f' s"
      by (metis assms(1,2,4) f_transformed_with_unequal_values' m powr_eq_0_iff powr_gt_zero)
    then show ?thesis using set_of_eq
      by (smt (z3) assms(1,3) atLeastAtMost_iff divide_left_mono divide_less_0_iff g m
          mult_neg_neg transfer_enclosure)
  qed
qed

lemma enclosure_with_inside_zero: (* x \<in> (-\<infinity>, m - f m / \<down>F'] \<union> [m - f m / \<up>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> 0 < upper F'" "f m < 0"
  shows "x \<le> m - f m / lower F' \<or> x \<ge> m - f m / upper F'" 
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume l: "x < m"
    then obtain s where s: "s \<in> {x..m}" "x = m - f m / f' s"
      by (metis assms(1,2,4) f_transformed_with_unequal_values m powr_eq_0_iff powr_gt_zero)
    have "f' s < 0" using assms(4) divide_nonpos_nonneg[of "f m" "f' s"] l s(2)
      by (smt divide_nonneg_nonneg)
    then have "x \<le> m - f m / lower F' \<or> x \<ge> m - f m / upper F'"
      using assms s transfer_enclosure[where x = s, of x m] m
      by (smt (z3) atLeastAtMost_iff divide_left_mono_neg mult_neg_neg set_of_eq)
    with s(2) show ?thesis by simp
  next
    assume "x = m"
    then show ?thesis using assms(2) by auto 
  next
    assume g: "x > m"
    then obtain s where s: "s \<in> {m..x} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values' m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,4) atLeastAtMost_iff diff_divide_distrib divide_right_mono_neg frac_less2 g m
          transfer_enclosure) 
  qed
qed

lemma enclosure_with_inside_zero': (* x \<in> (-\<infinity>, m - f m / \<up>F'] \<union> [m - f m / \<down>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> 0 < upper F'" "f m > 0"
  shows "x \<le> m - f m / upper F' \<or> x \<ge> m - f m / lower F'"
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume l: "x < m"
    then obtain s where s: "s \<in> {x..m} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,4) atLeastAtMost_iff diff_divide_distrib divide_right_mono_neg frac_less2 l m
          transfer_enclosure) 
  next
    assume "x = m"
    then show ?thesis using assms(2) by auto 
  next
    assume g: "x > m"
    then obtain s where s: "s \<in> {m..x}" "x = m - f m / f' s"
      by (metis assms(1,2,4) f_transformed_with_unequal_values' m powr_eq_0_iff powr_gt_zero)
    have "f' s < 0" using assms(4) divide_nonpos_nonneg[of "f m" "f' s"] g s(2)
      by (smt divide_nonneg_nonneg)
    then have "x \<le> m - f m / upper F' \<or> x \<ge> m - f m / lower F'"
      using assms s transfer_enclosure[where x = s, of x m] m
      by (smt (z3) atLeastAtMost_iff divide_left_mono mult_neg_neg set_of_eq transfer_enclosure)
    with s(2) show ?thesis by simp
  qed
qed

lemma enclosure_with_lower_zero: (* x \<in> [m - f m / \<up>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' = 0 \<and> 0 < upper F'" "f m < 0"
  shows "x \<ge> m - f m / upper F'"
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume l: "x < m"
    then obtain s where s: "s \<in> {x..m} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,3,4) atLeastAtMost_iff divide_nonpos_nonneg l m transfer_enclosure)
  next
    assume "x = m"
    then show ?thesis using assms(2) by auto 
  next
    assume g: "x > m"
    then obtain s where s: "s \<in> {m..x} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values' m by fastforce 
    then show ?thesis using set_of_eq
      by (smt (z3) assms(1,3) atLeastAtMost_iff divide_left_mono_neg divide_less_0_iff g m
          mult_pos_pos transfer_enclosure) 
  qed
qed

lemma enclosure_with_lower_zero': (* x \<in> (-\<infinity>, m - f m / \<up>F'] *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' = 0 \<and> 0 < upper F'" "f m > 0"
  shows "x \<le> m - f m / upper F'"
proof -
  have "x < m \<or> x = m \<or> x > m" by auto
  then show ?thesis
  proof (elim disjE)
    assume l: "x < m"
    then obtain s where s: "s \<in> {x..m} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,4) atLeastAtMost_iff divide_nonneg_nonpos frac_le l m transfer_enclosure) 
  next
    assume "x = m"
    then show ?thesis using assms(2) by auto 
  next
    assume g: "x > m"
    then obtain s where s: "s \<in> {m..x} \<and> x = m - f m / f' s"
      using assms(1,2,4) f_transformed_with_unequal_values' m by fastforce
    then show ?thesis using set_of_eq
      by (smt assms(1,3,4) atLeastAtMost_iff divide_nonneg_nonneg g m transfer_enclosure) 
  qed
qed

end

subsection "f(m) is an Interval"

locale newton_step_locale' = newton_step_locale +
  fixes F :: "real interval"
  assumes f_enclosure: "f m \<in> set_of F"

begin

lemma f'enclosure_not_zero:
  assumes "x \<in> set_of X" "f x = 0" "0 \<notin> set_of F'"
  shows "x \<in> set_of (interval_of m - F * inverse_interval' F')"
proof -
  have subset: "set_of (interval_of m - interval_of (f m) * inverse_interval' F')
                \<subseteq> set_of (interval_of m - F * inverse_interval' F')"
  proof -
    have "set_of (interval_of (f m)) \<subseteq> set_of F" using f_enclosure by (auto simp: set_of_eq)
    then show ?thesis by (simp add: set_of_mul_inc_left set_of_sub_inc_right)
  qed
  have "x \<in> set_of (interval_of m - interval_of (f m) * inverse_interval' F')"
    using assms(1-3) enclosure_not_zero m by auto
  then show ?thesis using subset by auto
qed

lemma f'enclosure_with_upper_zero: (* x \<in> (-\<infinity>, m - \<up>F / \<down>F'] *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> upper F' = 0" "upper F < 0"
  shows "x \<le> m - upper F / lower F'"
proof -
  have x: "x \<le> m - f m / lower F'"
    using assms enclosure_with_upper_zero f_enclosure sign_of_element by auto
  have "m - f m / lower F' \<le> m - upper F / lower F'"
    by (metis assms(3) atLeastAtMost_iff diff_left_mono divide_right_mono_neg f_enclosure
        lower_le_upper set_of_eq)
  then show ?thesis using x by simp
qed

lemma f'enclosure_with_upper_zero': (* x \<in> [m - \<down>F / \<up>F, \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> upper F' = 0" "0 < lower F"
  shows "x \<ge> m - lower F / lower F'"
proof -
  have x: "x \<ge> m - f m / lower F'"
    using assms enclosure_with_upper_zero' f_enclosure sign_of_element' by auto
  have "m - f m / lower F' \<ge> m - lower F / lower F'"
    by (metis assms(3) atLeastAtMost_iff diff_left_mono divide_right_mono_neg f_enclosure
        lower_le_upper set_of_eq)
  then show ?thesis using x by simp
qed

lemma f'enclosure_with_inside_zero: (* x \<in> (-\<infinity>, m - \<up>F / \<down>F'] \<union> [m - \<up>F / \<up>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> 0 < upper F'" "upper F < 0"
  shows "x \<le> m - upper F / lower F' \<or> x \<ge> m - upper F / upper F'"
proof -
  have x: "x \<le> m - f m / lower F' \<or> x \<ge> m - f m / upper F'"
    using assms f_enclosure enclosure_with_inside_zero newton_step_locale_axioms sign_of_element by blast
  have "m - f m / lower F' \<le> m - upper F / lower F' \<and> m - f m / upper F' \<ge> m - upper F / upper F'"
    by (metis assms(3) atLeastAtMost_iff diff_left_mono divide_right_mono divide_right_mono_neg
        f_enclosure le_less set_of_eq)
  then show ?thesis using x by auto
qed

lemma f'enclosure_with_inside_zero': (* x \<in> (-\<infinity>, m - \<down>F / \<up>F'] \<union> [m - \<down>F / \<down>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' < 0 \<and> 0 < upper F'" "0 < lower F"
  shows "x \<le> m - lower F / upper F' \<or> x \<ge> m - lower F / lower F'"
proof -
  have x: "x \<le> m - f m / upper F' \<or> x \<ge> m - f m / lower F'"
    using assms f_enclosure enclosure_with_inside_zero' newton_step_locale_axioms sign_of_element' by blast
  have "m - f m / lower F' \<ge> m - lower F / lower F' \<and> m - f m / upper F' \<le> m - lower F / upper F'"
    by (metis assms(3) atLeastAtMost_iff diff_left_mono divide_right_mono divide_right_mono_neg
        f_enclosure le_less set_of_eq)
  then show ?thesis using x by auto
qed

lemma f'enclosure_with_lower_zero: (* x \<in> m - fm / F' = [m - \<up>F / \<up>F', \<infinity>) *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' = 0 \<and> 0 < upper F'" "upper F < 0"
  shows "x \<ge> m - upper F / upper F'"
proof -
  have x: "x \<ge> m - f m / upper F'"
    using assms enclosure_with_lower_zero f_enclosure sign_of_element by auto 
  have "m - f m / upper F' \<ge> m - upper F / upper F'"
    by (metis assms(3) atLeastAtMost_iff diff_left_mono divide_le_cancel f_enclosure le_cases set_of_eq)
  then show ?thesis using x by simp
qed

lemma f'enclosure_with_lower_zero': (* x \<in> (-\<infinity>, m - \<down>F / \<up>F'] *)
  assumes "x \<in> set_of X" "f x = 0" "lower F' = 0 \<and> 0 < upper F'" "0 < lower F"
  shows "x \<le> m - lower F / upper F'"
proof -
  have x: "x \<le> m - f m / upper F'"
    using assms enclosure_with_lower_zero' f_enclosure sign_of_element' by auto 
  have "m - f m / upper F' \<le> m - lower F / upper F'"
    by (metis assms(3) atLeastAtMost_iff diff_left_mono divide_le_cancel f_enclosure le_cases set_of_eq)
  then show ?thesis using x by simp
qed

end

section "Newton Steps"

subsection "newton_step (real)"

text "In the thesis, this proof is not used, as we are working on floats.
However, for possible future work, the proof is left in here.
Also, it makes understanding the following proof of the Newton step on floats easier."

definition newton_step:: "real interval \<Rightarrow> real interval \<Rightarrow> real interval \<Rightarrow> real \<Rightarrow> real interval list" where
"newton_step X F F' m  = (
  if lower F' = 0 \<and> upper F' = 0 then (if 0 \<in> set_of F then [X] else [])
  else if 0 < lower F' \<or> upper F' < 0 then interval_intersection X (interval_of m - F * inverse_interval' F')
  else if upper F' = 0 then (
    if upper F < 0 then interval_intersection_unbounded_lower X (m - upper F / lower F')
    else if 0 < lower F then interval_intersection_unbounded_upper X (m - lower F / lower F')
    else split_interval X m
  )
  else if lower F' = 0 then (
    if upper F < 0 then interval_intersection_unbounded_upper X (m - upper F / upper F')
    else if 0 < lower F then interval_intersection_unbounded_lower X (m - lower F / upper F')
    else split_interval X m
  )
  else (
    if upper F < 0 then interval_intersection_unbounded_lower X (m - upper F / lower F')
      @ interval_intersection_unbounded_upper X (m - upper F / upper F')
    else if 0 < lower F then interval_intersection_unbounded_lower X (m - lower F / upper F')
      @ interval_intersection_unbounded_upper X (m - lower F / lower F')
    else split_interval X m
  )
)"

locale newton_step_locale_real =
  fixes f f' :: "real \<Rightarrow> real"
  fixes X F' F :: "real interval"
  fixes m :: "real"
  assumes f' : "x \<in> set_of X \<Longrightarrow> (f has_field_derivative f' x)(at x within set_of X)"
  assumes f'_enclosure : "x \<in> set_of X \<Longrightarrow> f' x \<in> set_of F'"
  assumes m : "m \<in> set_of X"
  assumes f_enclosure : "f m \<in> set_of F"

begin

interpretation newton_step_locale' f f' X F' m F
proof
  show "\<And>x. x \<in>\<^sub>i X \<Longrightarrow> (f has_real_derivative f' x) (at x within set_of X)" by (simp add: f')
  show "\<And>x. x \<in>\<^sub>i X \<Longrightarrow> f' x \<in>\<^sub>i F'" by (simp add: f'_enclosure)
  show "m \<in>\<^sub>i X" by (simp add: m) 
  show "f m \<in>\<^sub>i F " by (simp add: f_enclosure) 
qed

lemma newton_step_correctness:
  fixes x::real
  assumes "x \<in> set_of X" "f x = 0"
  shows "x \<in> set_of_interval_list (newton_step X F F' m)"
proof -
  consider (z) "lower F' = 0" "upper F' = 0" | (nz) "lower F' > 0 \<or> upper F' < 0"
    | (upz) "lower F' < 0" "upper F' = 0" | (lwz) "lower F' = 0" "upper F' > 0"
    | (btw) "lower F' < 0" "upper F' > 0" by linarith
  then show ?thesis
  proof cases
    case z
    then show ?thesis
    proof (cases "0 \<in> set_of F")
      case True
      then show ?thesis using z True newton_step_def assms(1) by simp
    next
      case False
      have "\<forall>x \<in> set_of X. f' x = 0"
        by (smt (z3) atLeastAtMost_iff f'_enclosure set_of_eq z)
      then have "\<forall>x \<in> set_of X. \<forall> x' \<in> set_of X. f x = f x'" using deriv_is_zero
        by (smt (z3) atLeastAtMost_iff mult_eq_0_iff set_of_eq transfer_mvt)
      then have "\<forall>x \<in> set_of X. f x \<noteq> 0" using False f_enclosure m by fastforce 
      then show ?thesis using z False newton_step_def assms(1,2) by auto
    qed
  next
    case nz
    then have "x \<in> set_of (interval_of m - F * inverse_interval' F')"
      using f'enclosure_not_zero assms sign_of_element sign_of_element' by blast 
    then have "x \<in> set_of_interval_list (interval_intersection X (interval_of m - F * inverse_interval' F'))"
      by (simp add: assms(1) in_both_intervals_in_intersection)
    then show ?thesis using newton_step_def nz by auto
  next
    case upz
    then have "upper F < 0 \<or> 0 < lower F \<or> 0 \<in> set_of F" by (auto simp: set_of_eq)
    then show ?thesis
    proof (elim disjE)
      assume fneg: "upper F < 0"
      then have "x \<le> m - upper F / lower F'"
        using f'enclosure_with_upper_zero assms upz by (simp add: set_of_eq)
      then have "x \<in> set_of_interval_list (interval_intersection_unbounded_lower X (m - upper F / lower F'))"
        using in_both_intervals_in_ul_intersection assms by (simp add: set_of_eq)
      then show ?thesis using upz fneg newton_step_def by auto
    next
      assume fpos: "0 < lower F"
      then have "m - lower F / lower F' \<le> x"
        using f'enclosure_with_upper_zero' assms upz by (simp add: set_of_eq)
      then have "x \<in> set_of_interval_list (interval_intersection_unbounded_upper X (m - lower F / lower F'))"
        using in_both_intervals_in_uu_intersection assms by (simp add: set_of_eq)
      then show ?thesis using upz fpos newton_step_def f_enclosure sign_of_element sign_of_element'
        by fastforce
    next
      assume fz: "0 \<in> set_of F"
      then show ?thesis using upz newton_step_def assms(1) split_same_set by (simp add: set_of_eq)
    qed
  next
    case lwz
    then have "upper F < 0 \<or> 0 < lower F \<or> 0 \<in> set_of F" by (auto simp: set_of_eq)
    then show ?thesis
    proof (elim disjE)
      assume fneg: "upper F < 0"
      then have "m - upper F / upper F' \<le> x"
        using f'enclosure_with_lower_zero assms lwz by (simp add: set_of_eq)
      then have "x \<in> set_of_interval_list (interval_intersection_unbounded_upper X (m - upper F / upper F'))"
        using in_both_intervals_in_uu_intersection assms by (simp add: set_of_eq)
      then show ?thesis using lwz fneg newton_step_def by auto
    next
      assume fpos: "0 < lower F"
      then have "x \<le> m - lower F / upper F'"
        using f'enclosure_with_lower_zero' assms lwz by (simp add: set_of_eq)
      then have "x \<in> set_of_interval_list (interval_intersection_unbounded_lower X (m - lower F / upper F'))"
        using in_both_intervals_in_ul_intersection assms by (simp add: set_of_eq)
      then show ?thesis using lwz fpos newton_step_def f_enclosure sign_of_element sign_of_element'
        by fastforce
    next
      assume fz: "0 \<in> set_of F"
      then show ?thesis using lwz fz newton_step_def assms(1) split_same_set by (simp add: set_of_eq)
    qed
  next
    case btw
    then have "upper F < 0 \<or> 0 < lower F \<or> 0 \<in> set_of F" by (auto simp: set_of_eq)
    then show ?thesis
    proof (elim disjE)
      assume fneg: "upper F < 0"
      then have "m - upper F / upper F' \<le> x \<or> x \<le> m - upper F / lower F'"
        using f'enclosure_with_inside_zero assms btw set_of_eq by blast
      then have "x \<in> set_of_interval_list (interval_intersection_unbounded_lower X (m - upper F / lower F')
          @ interval_intersection_unbounded_upper X (m - upper F / upper F'))"
        using in_both_intervals_in_ul_intersection in_both_intervals_in_uu_intersection assms
              in_larger_interval_list_set_l in_larger_interval_list_set_r by auto  
      then show ?thesis using btw fneg newton_step_def by auto
    next
      assume fpos: "0 < lower F"
      then have "m - lower F / lower F' \<le> x \<or> x \<le> m - lower F / upper F'"
        using f'enclosure_with_inside_zero' assms btw set_of_eq by blast
      then have "x \<in> set_of_interval_list (interval_intersection_unbounded_lower X (m - lower F / upper F')
          @ interval_intersection_unbounded_upper X (m - lower F / lower F'))"
        using in_both_intervals_in_ul_intersection in_both_intervals_in_uu_intersection assms
          in_larger_interval_list_set_l in_larger_interval_list_set_r by auto 
      then show ?thesis using btw fpos newton_step_def f_enclosure sign_of_element sign_of_element'
        by fastforce
    next
      assume fz: "0 \<in> set_of F"
      then show ?thesis using btw fz newton_step_def assms(1) split_same_set by (simp add: set_of_eq)
    qed
  qed
qed

end

subsection "newton_step_float"

definition newton_step_float:: "nat \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> float interval
  \<Rightarrow> float \<Rightarrow> float interval list" where
"newton_step_float prec X F F' m = (
  if lower F' = 0 \<and> upper F' = 0 then (if 0 \<in> set_of F then [X] else [])
  else if 0 < lower F' \<or> upper F' < 0 then
    float_interval_intersection X (plus_float_interval prec (interval_of m) (
      - mult_float_interval prec F (inverse_float_interval' prec F'))
    )
  else if upper F' = 0 then (
    if upper F < 0 then float_interval_intersection_unbounded_lower X (
      float_plus_up prec m (- float_divl prec (upper F) (lower F'))
    )
    else if 0 < lower F then float_interval_intersection_unbounded_upper X (
      float_plus_down prec m (- float_divr prec (lower F) (lower F'))
    )
    else split_float_interval X m
  )
  else if lower F' = 0 then (
    if upper F < 0 then float_interval_intersection_unbounded_upper X (
      float_plus_down prec m (- float_divr prec (upper F) (upper F'))
    )
    else if 0 < lower F then float_interval_intersection_unbounded_lower X (
      float_plus_up prec m (- float_divl prec (lower F) (upper F'))
    )
    else split_float_interval X m
  )
  else (
    if upper F < 0 then float_interval_intersection_unbounded_lower X (
      float_plus_up prec m (- float_divl prec (upper F) (lower F'))
    ) @ float_interval_intersection_unbounded_upper X (
      float_plus_down prec m (- float_divr prec (upper F) (upper F'))
    )
    else if 0 < lower F then float_interval_intersection_unbounded_lower X (
      float_plus_up prec m (- float_divl prec (lower F) (upper F'))
    ) @ float_interval_intersection_unbounded_upper X (
      float_plus_down prec m (- float_divr prec (lower F) (lower F'))
    )
    else split_float_interval X m
  )
)"

locale newton_step_locale_float =
  fixes f f' :: "real \<Rightarrow> real"
  fixes X F F' :: "float interval"
  fixes m :: "float"
  assumes f': "x \<in> set_of (real_interval X) \<Longrightarrow> (f has_field_derivative f' x)(at x within set_of (real_interval X))"
  assumes f'_enclosure: "x \<in> set_of (real_interval X) \<Longrightarrow> f' x \<in> set_of (real_interval F')"
  assumes m: "m \<in> set_of X"
  assumes f_enclosure: "f m \<in> set_of (real_interval F)"

begin

interpretation newton_step_locale_real f f' "real_interval X" "real_interval F'" "real_interval F" "real_of_float m"
proof
  show "\<And>x. x \<in>\<^sub>r X \<Longrightarrow> (f has_real_derivative f' x) (at x within set_of (real_interval X))" using f' by simp
  show "\<And>x. x \<in>\<^sub>r X \<Longrightarrow> f' x \<in>\<^sub>r F'" using f'_enclosure by simp
  show "real_of_float m \<in>\<^sub>r X" by (metis atLeastAtMost_iff in_real_intervalI less_eq_float.rep_eq m set_of_eq)
  show "f (real_of_float m) \<in>\<^sub>r F" by (simp add: f_enclosure)
qed

interpretation newton_step_locale' f f' "real_interval X" "real_interval F'" "real_of_float m" "real_interval F"
proof
  show "\<And>x. x \<in>\<^sub>r X \<Longrightarrow> (f has_real_derivative f' x) (at x within set_of (real_interval X))"
    by (simp add: f') 
  show "\<And>x. x \<in>\<^sub>r X \<Longrightarrow> f' x \<in>\<^sub>r F'" by (simp add: f'_enclosure)
  show "real_of_float m \<in>\<^sub>r X" by (simp add: m) 
  show "f (real_of_float m) \<in>\<^sub>r F" by (simp add: f_enclosure)
qed

lemma newton_step_float_correctness:
  fixes x :: real
  assumes "x \<in> set_of (real_interval X)" "f x = 0"
  shows "x \<in> real_set_of_float_interval_list (newton_step_float prec X F F' m)"
proof -
  consider (z) "lower F' = 0" "upper F' = 0" | (nz) "0 < lower F' \<or> upper F' < 0"
    | (upz) "lower F' < 0" "upper F' = 0"    | (lwz) "lower F' = 0" "upper F' > 0"
    | (btw) "lower F' < 0" "0 < upper F'" by linarith
  then show ?thesis
  proof cases
    case z
    then show ?thesis
    proof (cases "0 \<in> set_of F")
      case True
      then show ?thesis using z True newton_step_float_def assms(1) by simp
    next
      case False
      have "\<forall>x \<in> set_of (real_interval X). f' x = 0"
        by (smt (z3) atLeastAtMost_iff f'_enclosure lower_real_interval set_of_eq
            upper_real_interval z zero_float.rep_eq)
      then have const: "f x = f x'" if "x \<in> set_of (real_interval X)" "x' \<in> set_of (real_interval X)" for x x'
        using deriv_is_zero that by (smt (z3) atLeastAtMost_iff mult_eq_0_iff set_of_eq transfer_mvt)
      have "f m \<noteq> 0"
        using m f_enclosure False by (metis atLeastAtMost_iff less_eq_float.rep_eq
            lower_real_interval set_of_eq upper_real_interval zero_float.rep_eq)
      also have "f m = f x"
        using m assms(1) by (intro const) (auto simp: set_of_eq)
      also have "f x = 0"
        using assms(2) .
      finally show ?thesis by simp
    qed
  next
    case nz
    then have "x \<in> set_of (interval_of m - real_interval F * inverse_interval' (real_interval F'))"
      using f'enclosure_not_zero assms sign_of_element sign_of_element'
      by (smt (z3) less_float.rep_eq lower_real_interval upper_real_interval zero_float.rep_eq)
    also have "0 \<notin> set_of F'"
      using nz by (metis atLeastAtMost_iff not_le set_of_eq)
    hence "interval_of (real_of_float m) - real_interval F * inverse_interval' (real_interval F') \<le>
           real_interval (interval_of m - mult_float_interval prec F (inverse_float_interval' prec F'))"
      by (intro diff_mono_real_interval mult_float_interval_mono order.refl inverse_float_interval'_mono) auto
    hence "set_of (interval_of m - real_interval F * inverse_interval' (real_interval F')) \<subseteq>
           set_of (real_interval (interval_of m - mult_float_interval prec F (inverse_float_interval' prec F')))"
      by (meson less_eq_interval_def set_of_subset_iff)
    finally have "x \<in> set_of (real_interval (interval_of m - mult_float_interval prec F (inverse_float_interval' prec F')))"
      by (simp add: set_of_eq)
    then have "x \<in> set_of (real_interval (plus_float_interval prec (interval_of m) (
      - mult_float_interval prec F (inverse_float_interval' prec F'))))"
      using minus_float_interval_monotonic real_interval_subset by (meson set_of_subset_iff' subset_iff)
    then show ?thesis unfolding newton_step_float_def
      using nz assms(1) in_both_float_intervals_in_float_intersection' by auto 
  next
    case upz
    then have "upper F < 0 \<or> 0 < lower F \<or> 0 \<in> set_of F" by (auto simp: set_of_eq)
    then show ?thesis
    proof (elim disjE)
      assume fneg: "upper F < 0"
      then have "x \<le> m - upper F / lower F'"
        using f'enclosure_with_upper_zero assms upz by (simp add: set_of_eq)
      then have "x \<le> m - float_divl prec (upper F) (lower F')"
        by (smt float_divl less_eq_float.rep_eq minus_float.rep_eq)
      then have "x \<le> float_plus_up prec m (- float_divl prec (upper F) (lower F'))"
        using float_plus_up_le by auto
      then have "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_lower X (
          float_plus_up prec m (- float_divl prec (upper F) (lower F'))))"
        using in_both_float_intervals_in_ul_intersection' assms by (auto simp: set_of_eq)
      then show ?thesis using upz fneg newton_step_float_def by auto
    next
      assume fpos: "0 < lower F"
      then have "m - lower F / lower F' \<le> x"
        using f'enclosure_with_upper_zero' assms upz by (simp add: set_of_eq)
      then have "m - float_divr prec (lower F) (lower F') \<le> x"
        by (smt float_divr less_eq_float.rep_eq minus_float.rep_eq)
      then have "float_plus_down prec m (- float_divr prec (lower F) (lower F')) \<le> x"
        using float_plus_down_le by auto
      then have "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_upper X (
        float_plus_down prec m (- float_divr prec (lower F) (lower F'))))"
        using in_both_float_intervals_in_uu_intersection' assms by (simp add: set_of_eq)
      then show ?thesis using upz fpos newton_step_float_def
        by (smt (z3) less_eq_float.rep_eq less_float.rep_eq lower_le_upper)
    next
      assume fz: "0 \<in> set_of F"
      then show ?thesis using upz split_float_same_set' newton_step_float_def assms(1)
        by (simp add: set_of_eq)
    qed
  next
    case lwz
    then have "upper F < 0 \<or> 0 < lower F \<or> 0 \<in> set_of F" by (auto simp: set_of_eq)
    then show ?thesis
    proof (elim disjE)
      assume fneg: "upper F < 0"
      then have "m - upper F / upper F' \<le> x"
        using f'enclosure_with_lower_zero assms lwz by (simp add: set_of_eq)
      then have "m - float_divr prec (upper F) (upper F') \<le> x"
        by (smt float_divr less_eq_float.rep_eq minus_float.rep_eq)
      then have "float_plus_down prec m (- float_divr prec (upper F) (upper F')) \<le> x"
        using float_plus_down_le by auto
      then have "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_upper X (
        float_plus_down prec m (- float_divr prec (upper F) (upper F'))))"
        using in_both_float_intervals_in_uu_intersection' assms by (simp add: set_of_eq)
      then show ?thesis using lwz fneg newton_step_float_def by auto
    next
      assume fpos: "0 < lower F"
      then have "x \<le> m - lower F / upper F'"
        using f'enclosure_with_lower_zero' assms lwz by (simp add: set_of_eq)
      then have "x \<le> m - float_divl prec (lower F) (upper F')"
        by (smt float_divl less_eq_float.rep_eq minus_float.rep_eq)
      then have "x \<le> float_plus_up prec m (- float_divl prec (lower F) (upper F'))"
        using float_plus_up_le by auto
      then have "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_lower X (
        float_plus_up prec m (- float_divl prec (lower F) (upper F'))))"
        using in_both_float_intervals_in_ul_intersection' assms by (simp add: set_of_eq)
      then show ?thesis using lwz fpos newton_step_float_def
        by (smt (z3) less_eq_float.rep_eq less_float.rep_eq lower_le_upper)
    next
      assume fz: "0 \<in> set_of F"
      then show ?thesis using lwz split_float_same_set' newton_step_float_def assms(1)
        by (simp add: set_of_eq)
    qed
  next
    case btw
    then have "upper F < 0 \<or> 0 < lower F \<or> 0 \<in> set_of F" by (auto simp: set_of_eq)
    then show ?thesis
    proof (elim disjE)
      assume fneg: "upper F < 0"
      then have "m - upper F / upper F' \<le> x \<or> x \<le> m - upper F / lower F'"
        using f'enclosure_with_inside_zero assms btw by (auto simp: set_of_eq)
      then have "m - float_divr prec (upper F) (upper F') \<le> x \<or> x \<le> m - float_divl prec (upper F) (lower F')"
        by (smt float_divl float_divr less_eq_float.rep_eq minus_float.rep_eq)
      then have "float_plus_down prec m (- float_divr prec (upper F) (upper F')) \<le> x
        \<or> x \<le> float_plus_up prec m (- float_divl prec (upper F) (lower F'))"
        using float_plus_down_le float_plus_up_le by auto
      then have "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_lower X (
        float_plus_up prec m (- float_divl prec (upper F) (lower F')))
        @ float_interval_intersection_unbounded_upper X (
        float_plus_down prec m (- float_divr prec (upper F) (upper F'))))"
        using in_both_float_intervals_in_ul_intersection' in_both_float_intervals_in_uu_intersection' assms
              in_larger_real_set_of_float_interval_list_l in_larger_real_set_of_float_interval_list_r by auto
      then show ?thesis using btw fneg newton_step_float_def by auto
    next
      assume fpos: "0 < lower F"
      then have "m - lower F / lower F' \<le> x \<or> x \<le> m - lower F / upper F'"
        using f'enclosure_with_inside_zero' assms btw by (auto simp: set_of_eq)
      then have "m - float_divr prec (lower F) (lower F') \<le> x \<or> x \<le> m - float_divl prec (lower F) (upper F')"
        by (smt float_divl float_divr less_eq_float.rep_eq minus_float.rep_eq) 
      then have "float_plus_down prec m (- float_divr prec (lower F) (lower F')) \<le> x
        \<or> x \<le> float_plus_up prec m (- float_divl prec (lower F) (upper F'))"
        using float_plus_down_le float_plus_up_le by auto
      then have "x \<in> real_set_of_float_interval_list (float_interval_intersection_unbounded_lower X (
        float_plus_up prec m (- float_divl prec (lower F) (upper F')))
        @ float_interval_intersection_unbounded_upper X (
        float_plus_down prec m (- float_divr prec (lower F) (lower F'))))"
        using in_both_float_intervals_in_ul_intersection' in_both_float_intervals_in_uu_intersection' assms
              in_larger_real_set_of_float_interval_list_l in_larger_real_set_of_float_interval_list_r by auto
      then show ?thesis using btw fpos newton_step_float_def
        by (smt (z3) less_eq_float.rep_eq less_float.rep_eq lower_le_upper)
    next
      assume fz: "0 \<in> set_of F"
      then show ?thesis using btw split_float_same_set' newton_step_float_def assms(1) by (simp add: set_of_eq)
    qed
  qed
qed

end

subsection "newton_step_floatarith"

definition newton_step_floatarith:: "floatarith \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval list option" where
"newton_step_floatarith f prec ivl = do {
  let m = float_down prec (mid ivl);
  let f' = DERIV_floatarith 0 f;
  F \<leftarrow> approx prec f [Some (interval_of m)];
  F' \<leftarrow> approx prec f' [Some ivl];
  if m \<le> lower ivl then Some [round_interval prec ivl]
  else if isDERIV_approx prec 0 f [Some ivl] then
     Some (map (round_interval prec) (newton_step_float prec ivl F F' m)) else None
}"

lemma newton_step_floatarith_correctness:
  fixes x :: real
  assumes "newton_step_floatarith f prec ivl = Some ivls"
    "interpret_floatarith f [x] = 0"
    "x \<in> set_of (real_interval ivl)"
  defines "m \<equiv> float_down prec (mid ivl)"
  shows "x \<in> real_set_of_float_interval_list ivls"
proof (cases "m \<le> lower ivl")
  case True
  then have "ivls = [round_interval prec ivl]"
    using assms unfolding newton_step_floatarith_def m_def by (simp add: bind_eq_Some_conv)
  then show ?thesis by (simp add: assms(3) in_round_intervalI)
next
  case False
  from False have m: "m > lower ivl"
    by (auto simp: not_le)
  define f' where "f' = DERIV_floatarith 0 f"
  obtain F' where F': "approx prec f' [Some ivl] = Some F'"
    using assms(1) by (force simp: newton_step_floatarith_def f'_def)
  obtain F where F: "approx prec f [Some (interval_of m)] = Some F"
    using assms(1) by (force simp: newton_step_floatarith_def m_def)
  have isDERIV_approx': "isDERIV_approx prec 0 f [Some ivl]"
    using assms(1) False F m unfolding newton_step_floatarith_def f'_def m_def
    by (auto simp: Let_def bind_eq_Some_conv split: if_splits)
  then show ?thesis
  proof -
    interpret newton_step_locale_float "\<lambda>x. interpret_floatarith f [x]" "\<lambda>x. interpret_floatarith f' [x]" ivl F F' m
    proof
      show "((\<lambda>x. interpret_floatarith f [x]) has_real_derivative interpret_floatarith f' [x])
            (at x within set_of (real_interval ivl))" if x: "x \<in>\<^sub>r ivl" for x
      proof -
        have "((\<lambda>x. interpret_floatarith f ([0][0 := x])) has_real_derivative interpret_floatarith f' ([0][0 := x]))(at x)"
          unfolding f'_def
          by (rule DERIV_floatarith[OF _ isDERIV_approx[OF _ isDERIV_approx']])
            (auto simp: bounded_by_def x)
        thus ?thesis by (auto intro: has_field_derivative_at_within)
      qed
      show "\<And>x. x \<in>\<^sub>r ivl \<Longrightarrow> interpret_floatarith f' [x] \<in>\<^sub>r F'"
        by (rule approx[OF _ F']) (auto simp: bounded_by_def)
      show "interpret_floatarith f [real_of_float m] \<in>\<^sub>r F"
        by (rule approx[OF _ F]) (auto simp: bounded_by_def)
      show "m \<in>\<^sub>i ivl"
      proof -
        have "float_down prec (mid ivl) \<le> upper ivl" using round_down mid_in_interval
          by (metis dual_order.trans float_down.rep_eq less_eq_float.rep_eq mid_le(2))
        then show ?thesis using False unfolding m_def by (metis assms(4) in_intervalI le_cases)
      qed
    qed
    have "x \<in> real_set_of_float_interval_list (newton_step_float prec ivl F F' m)"
      by (simp add: assms(2,3) newton_step_float_correctness)
    then have "x \<in> real_set_of_float_interval_list (map (round_interval prec) (newton_step_float prec ivl F F' m))"
      using in_rounded_interval_list by simp
    then show ?thesis using assms False F F' isDERIV_approx'
      unfolding newton_step_floatarith_def m_def f'_def by simp
  qed
qed
    
section "Recursive Method"

subsection "mapM"

fun mapM:: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
"mapM f [] = Some []" |
"mapM f (x#xs) = do {
  y \<leftarrow> f x;
  ys \<leftarrow> mapM f xs;
  Some (y # ys)
}"

lemma mapM_None: "mapM f xs = None \<longleftrightarrow> (\<exists>x\<in>set xs. f x = None)"
proof (induct xs)
  case (Cons x xs) thus ?case
    by (cases "f x", simp, cases "mapM f xs", auto)
qed simp

lemma mapM_Some: "mapM f xs = Some ys \<Longrightarrow> ys = map (\<lambda>x. the (f x)) xs \<and> (\<forall>x\<in>set xs. f x \<noteq> None)"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys) thus ?case
    by (cases "f x", simp, cases "mapM f xs", auto)
qed simp

lemma mapM_Some_idx:
  assumes some: "mapM f xs = Some ys" and i: "i < length xs"
  shows "\<exists>y. f (xs ! i) = Some y \<and> ys ! i = y"
proof -
  note m = mapM_Some [OF some]
  from m[unfolded set_conv_nth] i have "f (xs ! i) \<noteq> None" by auto
  then obtain y where "f (xs ! i) = Some y" by auto
  then have "f (xs ! i) = Some y \<and> ys ! i = y" unfolding m [THEN conjunct1] using i by auto
  then show ?thesis ..
qed

lemma mapM_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "mapM f xs = mapM g ys"
  unfolding assms(1) using assms(2) by (induct ys) auto

lemma mapM_map: "mapM f xs = (if (\<forall>x\<in>set xs. f x \<noteq> None) then Some (map (\<lambda>x. the (f x)) xs) else None)"
proof (cases "mapM f xs")
  case None
  thus ?thesis using mapM_None by auto
next
  case (Some ys)
  with mapM_Some [OF Some] show ?thesis by auto
qed

lemma mapM_mono [partial_function_mono]:
  fixes C :: "'a \<Rightarrow> ('b \<Rightarrow> 'c option) \<Rightarrow> 'd option"
  assumes C: "\<And>y. mono_option (C y)"
  shows "mono_option (\<lambda>f. mapM (\<lambda>y. C y f) B)"
proof (induct B)
  case Nil
  show ?case unfolding mapM.simps by (rule option.const_mono)
next
  case (Cons b B)
  show ?case unfolding mapM.simps
    by (rule bind_mono [OF C bind_mono [OF Cons option.const_mono]])
qed

lemma those_mono[partial_function_mono]:
  assumes "monotone option.le_fun (list_all2 option_ord) B"
  shows "mono_option (\<lambda>f. those (B f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b option" assume "option.le_fun f g"
  hence "list_all2 option_ord (B f) (B g)" using assms by (metis monotoneD)
  thus "option_ord (those (B f)) (those (B g))"
    by induction (auto simp: flat_ord_def split: option.splits)
qed

subsection "newton_floatarith"

partial_function (option) newton_floatarith::
  "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval list option" where
"newton_floatarith eps f prec ivl = (if width ivl < Float 1 (-eps) then Some [ivl] else do {
  ivls \<leftarrow> newton_step_floatarith f prec ivl;
  if ivls = [ivl] then Some [ivl]
  else do {
    ivls' \<leftarrow> mapM (newton_floatarith eps f prec) ivls;
    Some (concat ivls')
  }
})"

lemma Option_bind_altdef: "Option.bind x f = (case x of None \<Rightarrow> None | Some x' \<Rightarrow> f x')"
  by (cases x) auto

lemma newton_floatarith_correctness:
  fixes x :: real
  assumes "newton_floatarith eps f prec ivl = Some ivls"
          "interpret_floatarith f [x] = 0"
          "x \<in> set_of (real_interval ivl)"
  shows   "x \<in> real_set_of_float_interval_list ivls"
  using assms
proof (induction rule: newton_floatarith.raw_induct[rotated 1, consumes 1])
  case (1 newton_floatarith eps f prec ivl ivls)
  consider (stop) "ivls = [ivl]"
    | (rec) ivls' ivlss' where
        "newton_step_floatarith f prec ivl = Some ivls'"
        "mapM (newton_floatarith eps f prec) ivls' = Some ivlss'" "ivls = concat ivlss'"
    using 1(2) by (auto split: if_splits option.splits simp: Option_bind_altdef)
  thus ?case
  proof cases
    case stop
    thus ?thesis using 1 by auto
  next
    case (rec ivls' ivlss')
    then have "x \<in> real_set_of_float_interval_list ivls'"
      using "1.prems"(1,2) newton_step_floatarith_correctness by auto
    then obtain i where i: "x \<in> set_of (real_interval (ivls' ! i))" "i < length ivls'"
      using in_float_interval_list_in_set_of_float_interval' by blast
    obtain xivls where xivls: "newton_floatarith eps f prec (ivls' ! i) = Some xivls"
      using mapM_Some_idx local.rec(2) i(2) by blast
    then have x: "x \<in> real_set_of_float_interval_list xivls" using "1.IH" "1.prems"(1) i by auto
    have "Some ivlss' = Some (map (\<lambda>a. the ((newton_floatarith eps f prec) a)) ivls')"
      using mapM_Some by (metis local.rec(2))
    then have "xivls \<in> set ivlss'" by (metis xivls i(2) length_map nth_map nth_mem option.sel)
    then have "x \<in> real_set_of_float_interval_list (concat ivlss')"
      by (metis x concat.simps(2) concat_append in_larger_real_set_of_float_interval_list_l
          in_larger_real_set_of_float_interval_list_r in_set_conv_decomp)
    thus ?thesis by (simp add: local.rec(3))
  qed
qed

end