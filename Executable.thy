theory Executable
  imports Newton

begin

section "Lemmas to Enable Evaluation"
subsection "Code Lemmas"

lemmas newton_floatarith_simp_rules [code] = newton_floatarith.simps

lemma element_in_interval_bounds [code_unfold]: "x \<in> set_of ivl \<longleftrightarrow> (case bounds_of_interval ivl of (l, u) \<Rightarrow> l \<le> x \<and> x \<le> u)"
  unfolding set_of.rep_eq by auto

lemma interval''_order [code]: "bounds_of_interval (Interval'' lu) = (if fst lu \<le> snd lu then lu else (snd lu, fst lu))"
  unfolding Interval''_def by (auto simp: case_prod_unfold Interval_inverse split_beta')

lemma interval''_split [code]:
  "Interval_Help.split_float_interval ivl m =
     (if m \<in>\<^sub>i ivl then [Interval'' (lower ivl, m), Interval'' (m, upper ivl)] else [ivl])"
  unfolding Interval_Help.split_float_interval_def Interval''_def by (simp add: set_of_eq)

lemma float_interval''_intersection [code]:
  "float_interval_intersection ivl1 ivl2 =
     (if upper ivl2 < lower ivl1 \<or> upper ivl1 < lower ivl2 then []
      else [Interval'' (max (lower ivl1) (lower ivl2), min (upper ivl1) (upper ivl2))])"
  unfolding float_interval_intersection_def Interval''_def
  by (auto simp: min_def max_def simp: real_of_float_le_iff real_of_float_less_iff
           simp del: less_eq_float.rep_eq less_float.rep_eq)

lemma inverse_float_interval'' [code]:
  "Interval_Help.inverse_float_interval' prec ivl =
     Interval'' (float_divl prec 1 (upper ivl), float_divr prec 1 (lower ivl))"
  unfolding inverse_float_interval'_def by simp

lemma float_interval''_intersection_unbounded_lower [code]:
  "float_interval_intersection_unbounded_lower ivl u =
     (if u < lower ivl then [] else [Interval'' (lower ivl, min (upper ivl) u)])"
  unfolding float_interval_intersection_unbounded_lower_def Interval''_def
  by (auto simp: real_of_float_le_iff real_of_float_less_iff
           simp del: less_eq_float.rep_eq less_float.rep_eq)

lemma float_interval''_intersection_unbounded_upper [code]:
  "float_interval_intersection_unbounded_upper ivl u =
     (if upper ivl < u then [] else [Interval'' (max (lower ivl) u, upper ivl)])"
  unfolding float_interval_intersection_unbounded_upper_def Interval''_def
  by (auto simp: real_of_float_le_iff real_of_float_less_iff
           simp del: less_eq_float.rep_eq less_float.rep_eq)

subsection "Helper for floatariths"

instantiation floatarith :: plus
begin
definition "plus_floatarith = floatarith.Add"
instance ..
end

instantiation floatarith :: times
begin
definition "times_floatarith = floatarith.Mult"
instance ..
end

instantiation floatarith :: uminus
begin
definition "uminus_floatarith = floatarith.Minus"
instance ..
end

definition floatarith_Sin where "floatarith_Sin x = floatarith.Cos (floatarith.Num (Float 1 (-1)) * floatarith.Pi + (-x))"

subsection "Variations of the Newton Method for Testing"

text "Additional argument for maximum amount of iterations."

partial_function (option) newton_floatarith_max_its ::
  "nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval list option" where
"newton_floatarith_max_its its eps f prec ivl = (if its = 0 \<or> width ivl < Float 1 (-eps) then Some [ivl] else do {
  ivls \<leftarrow> newton_step_floatarith f prec ivl;
  if ivls = [ivl] then Some [ivl]
  else do {
    ivls' \<leftarrow> mapM (newton_floatarith_max_its (its - 1) eps f prec) ivls;
    Some (concat ivls')
  }
})"

lemmas newton_floatarith_max_rec_simp_rules [code] = newton_floatarith_max_its.simps

fun max_element :: "nat list \<Rightarrow> nat" where
"max_element [] = 0" |
"max_element (x#xs) = max x (max_element xs)"

text "Instead of intervals the result of this function is the amount of iterations."

partial_function (option) newton_floatarith_c_its ::
  "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> nat option" where
"newton_floatarith_c_its eps f prec ivl = (if width ivl < Float 1 (-eps) then Some 1 else do {
  ivls \<leftarrow> newton_step_floatarith f prec ivl;
  if ivls = [ivl] then Some 1
  else do {
    ivls' \<leftarrow> mapM (newton_floatarith_c_its eps f prec) ivls;
    Some (Suc (max_element ivls'))
  }
})"

lemmas newton_floatarith_rec_simp_rules [code] = newton_floatarith_c_its.simps

subsection "Helping Lemmas for Evaluation"

fun some_intervals_to_real::  "float interval list option \<Rightarrow> real interval list" where
"some_intervals_to_real None = []" |
"some_intervals_to_real (Some []) = []" |
"some_intervals_to_real (Some (ivl#ivls)) = real_interval ivl # some_intervals_to_real (Some ivls)"

fun some_intervals_to_width:: "float interval list option \<Rightarrow> real list" where
"some_intervals_to_width None = []" |
"some_intervals_to_width (Some []) = []" |
"some_intervals_to_width (Some (ivl#ivls)) = width (real_interval ivl) # some_intervals_to_width (Some ivls)"

definition newton_fa where "newton_fa   f ivl = some_intervals_to_real (newton_floatarith 30 f 30 ivl)"
definition newton_mi where "newton_mi i f ivl = some_intervals_to_real (newton_floatarith_max_its i 30 f 30 ivl)"
definition newton_ci where "newton_ci   f ivl = newton_floatarith_c_its 30 f 30 ivl"
definition newton_wd where "newton_wd   f ivl = some_intervals_to_width (newton_floatarith 30 f 30 ivl)"

section "Examples"

locale examples

begin

definition x     where "x = floatarith.Var 0"
definition pos   where "pos n = floatarith.Num n"
definition neg   where "neg n = pos (-n)"

definition ivl_d where "ivl_d = Interval'' (-10, 10)"

subsection "Basic Cases"

subsubsection "Polynomials"

definition  f_1  where  "f_1  = pos 0"
definition  f_2  where  "f_2  = pos 1"
definition  f_3  where  "f_3  = x"
definition  f_4  where  "f_4  = x + neg 1"
definition  f_5  where  "f_5  = (x + neg 1) * (x + pos 2)"
definition  f_6  where  "f_6  = (x + neg 1) * (x + pos 2) * (x + neg 3)"
definition  f_6' where  "f_6' = floatarith.Power x 3 + (neg 2) * floatarith.Power x 2 + (neg 5) * x + (pos 6)"
definition  f_6o where  "f_6o = x * x * x + (neg 2) * x * x + (neg 5) * x + (pos 6)"

definition f'_6  where "f'_6  = DERIV_floatarith 0 f_6"
definition f'_6' where "f'_6' = DERIV_floatarith 0 f_6'"
definition f'_6o where "f'_6o = DERIV_floatarith 0 f_6o"

subsubsection "Square Roots"

definition  f_7 where   "f_7 = x * x"
definition  f_8 where   "f_8 = x * x + neg 1"
definition  f_9 where   "f_9 = x * x + neg 2"
definition f_10 where  "f_10 = x * x + neg 3"
definition f_11 where  "f_11 = x * x + neg 4"
definition f_12 where  "f_12 = x * x + neg 5"

subsection "Advanced Cases"

definition f_13 where  "f_13 = floatarith.Power x 50"
definition f_14 where  "f_14 = floatarith_Sin x"
definition I_14 where  "I_14 = Interval'' (2, 4)"
definition f_15 where  "f_15 = floatarith.Ln x + neg 1"
definition I_15 where  "I_15 = Interval'' (1, 3)"
definition f_16 where  "f_16 = x * floatarith.Exp x + neg 23"
definition I_16 where  "I_16 = Interval'' (1, 3)"

subsection "Corner Cases"

subsubsection "Root not in Interval"

definition f_17  where  "f_17  = floatarith.Power x 2"
definition I_17  where  "I_17  = Interval'' (Float 1 (-30), 10)"
definition I_17' where  "I_17' = Interval'' (Float 1 (-50), 10)"
definition f_18  where  "f_18  = floatarith.Power x 2 + neg 2"
definition I_18  where  "I_18  = Interval'' (2 + Float 1 (-50), 10)"
definition I_18' where  "I_18' = Interval'' (2 + Float 1 (-100000), 10)"
definition f_19  where  "f_19  = floatarith_Sin (x + pos 1)"
definition I_19  where  "I_19  = Interval'' (-1 + Float 1 (-30) ,2)"
definition I_19' where  "I_19' = Interval'' (-1 + Float 1 (-50) ,2)"

subsubsection "Root at Bound of Interval"

definition f_20   where  "f_20   = x + pos 3"
definition I_20_1 where  "I_20_1 = Interval'' (-10, 3)"
definition I_20_2 where  "I_20_2 = Interval'' (-3, 10)"
definition f_21   where  "f_21   = floatarith.Power x 2 + neg 9"
definition I_21_1 where  "I_21_1 = Interval'' (-10, -3)"
definition I_21_2 where  "I_21_2 = Interval'' (-3, 0)"
definition I_21_3 where  "I_21_3 = Interval'' (0, 3)"
definition I_21_4 where  "I_21_4 = Interval'' (3, 10)"
definition f_22   where  "f_22   = floatarith_Sin x"
definition I_22_1 where  "I_22_1 = Interval'' (-2, 0)"
definition I_22_2 where  "I_22_2 = Interval'' (0, 2)"

subsubsection "Function Without Root, Converging to Zero"

definition f_23  where  "f_23  = floatarith.Inverse x"
definition I_23  where  "I_23  = Interval'' (-1000000, -500000)"
definition I_23' where  "I_23' = Interval'' (500000, 1000000)"
definition f_24  where  "f_24  = floatarith.Exp x"
definition I_24  where  "I_24  = Interval'' (-1000000, -500000)"

end

end