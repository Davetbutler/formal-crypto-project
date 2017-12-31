theory Uniform_Sampling
imports Cyclic_Group_SPMF "~~/src/HOL/Number_Theory/Cong"
begin 

consts q :: nat

(*General lemma for mapping using sample_uniform*)

lemma one_time_pad: assumes inj_on: "inj_on f {..<q}" and sur: "f ` {..<q} = {..<q}"  
shows "map_spmf f (sample_uniform q) = (sample_uniform q)"
(is "?lhs = ?rhs")
proof-
 have rhs: "?rhs = spmf_of_set ({..< q})" 
   by(auto simp add: sample_uniform_def)
 also have "map_spmf(\<lambda>s. f s) (spmf_of_set {..<q}) = spmf_of_set ((\<lambda>s. f s) ` {..<q})"
   by(simp add: inj_on)(*uses map_spmf_of_set_inj_on but is simp lemma*)
 also have "f ` {..<q} = {..<q}"
   apply(rule endo_inj_surj) by(simp, simp add: sur, simp add: inj_on)
ultimately show ?thesis using rhs by simp
qed

(*We now prove the above instantiation for the (y + b) case*)

lemma a: assumes 1:  "x < q" and 2: "x' < q" and 3: "((y :: nat) + x) mod q = (y + x') mod q"  
shows "x = x'"
proof-
have aa: "((y :: nat) + x) mod q = (y + x') mod q \<Longrightarrow> x mod q = x' mod q"
  proof-
  have 4: "((y:: nat) + x) mod q = (y + x') mod q \<Longrightarrow> [((y:: nat) + x) = (y + x')] (mod q)"
    by(simp add: cong_nat_def)
  have 5: "[((y:: nat) + x) = (y + x')] (mod q) \<Longrightarrow> [x = x'] (mod q)"
    by (simp add: cong_add_lcancel_nat)
  have 6: "[x = x'] (mod q) \<Longrightarrow> x mod q = x' mod q"
    by(simp add: cong_nat_def)
  then show ?thesis by(simp add: 3 4 5 6)
  qed
also have bb: "x mod q = x' mod q \<Longrightarrow> x = x'"
  by(simp add: 1 2)
ultimately show ?thesis by(simp add: 3) 
qed

lemma inj_uni_samp: "inj_on  (\<lambda>(b :: nat). (y + b) mod q ) {..<q}"
by(simp add: inj_on_def)(auto simp only: a)

lemma surj_uni_samp: assumes inj: "inj_on  (\<lambda>(b :: nat). (y + b) mod q ) {..<q}" 
shows "(\<lambda>(b :: nat). (y + b) mod q) ` {..< q} =  {..< q}" 
apply(rule endo_inj_surj) using inj by auto

lemma samp_uni_plus_one_time_pad: 
shows "map_spmf (\<lambda>b. (y + b) mod q) (sample_uniform q) = map_spmf id (sample_uniform q)"
using inj_uni_samp surj_uni_samp one_time_pad by simp

(*x*b case*) 

lemma mult_samp_eq: assumes 1: "coprime x q" and 2: "y < q" and 3: "y' < q" 
and 4: "x * y mod q = x * y' mod q" 
shows "y = y'"
proof-
have 5: "x*y mod q = x*y' mod q \<Longrightarrow> y mod q = y' mod q"
  proof-
  have "x*y mod q = x*y' mod q \<Longrightarrow> [x*y = x*y'] (mod q)"
    by(simp add: cong_nat_def)
  also have "[x*y = x*y'] (mod q) = [y = y'] (mod q)"
    by(simp add: cong_mult_lcancel_nat 1)
  also have "[y = y'] (mod q) \<Longrightarrow> y mod q = y' mod q"
    by(simp add: cong_nat_def)
  ultimately show ?thesis by(simp add: 4)
  qed
also have 6: "y mod q = y' mod q \<Longrightarrow> y = y'"
by(simp add: 2 3)
ultimately show ?thesis by(simp add: 4) 
qed

lemma inj_on_mult: assumes 1: "coprime x q" shows "inj_on (\<lambda> b. x*b mod q) {..<q}"
apply(auto simp add: inj_on_def)
using 1 by(simp only: mult_samp_eq)

lemma surj_on_mult: assumes coprime: "coprime x q" and inj: "inj_on (\<lambda> b. x*b mod q) {..<q}"
shows "(\<lambda> b. x*b mod q) ` {..< q} = {..< q}"
apply(rule endo_inj_surj) using coprime inj by auto

lemma mult_one_time_pad: assumes coprime: "coprime x q" 
shows "map_spmf (\<lambda> b. x*b mod q) (sample_uniform q) = map_spmf (\<lambda> b. b) (sample_uniform q)"
using inj_on_mult surj_on_mult one_time_pad coprime by simp

(*(y + x*b) case*)

lemma samp_uni_add_mult: assumes 1: "coprime x q" and 2: "xa < q" and 3: "ya < q" and 4: "(y + x * xa) mod q = (y + x * ya) mod q" shows "xa = ya"
proof-
have 5: "(y + x * xa) mod q = (y + x * ya) mod q \<Longrightarrow> xa mod q = ya mod q"
  proof-
  have "(y + x * xa) mod q = (y + x * ya) mod q \<Longrightarrow> [y + x*xa = y + x *ya] (mod q)"
    using cong_nat_def by blast
  also have "[y + x*xa = y + x *ya] (mod q) \<Longrightarrow> [xa = ya] (mod q)"
    by(simp add: cong_add_lcancel_nat)(simp add: "1" cong_mult_lcancel_nat)
  ultimately show ?thesis by(simp add: cong_nat_def 4)
  qed
also have "xa mod q = ya mod q \<Longrightarrow> xa = ya"
  by(simp add: 2 3)
ultimately show ?thesis by(simp add: 4)
qed

lemma inj_on_add_mult: assumes coprime: "coprime x q" shows "inj_on (\<lambda> b. (y + x*b) mod q) {..<q}"
apply(auto simp add: inj_on_def)
using coprime by(simp only: samp_uni_add_mult)

lemma surj_on_add_mult: assumes coprime: "coprime x q" and inj: "inj_on (\<lambda> b. (y + x*b) mod q) {..<q}" 
shows "(\<lambda> b. (y + x*b) mod q) ` {..< q} = {..< q}" 
apply(rule endo_inj_surj) using coprime inj by auto

lemma add_mult_one_time_pad: assumes coprime: "coprime x q" 
shows "map_spmf (\<lambda> b. (y + x*b) mod q) (sample_uniform q) = map_spmf(\<lambda> b. b) (sample_uniform q)"
using inj_on_add_mult surj_on_add_mult one_time_pad coprime by simp

(*(y - b) case*)

lemma inj_on_minus: "inj_on  (\<lambda>(b :: nat). (y + (q - b)) mod q ) {..<q}"
apply(auto simp add: inj_on_def) 
proof -
  fix x :: nat and ya :: nat
  assume 1: "x < q"
  assume 2: "ya < q"
  assume 3: "(y + q - x) mod q = (y + q - ya) mod q"
  have "\<forall>n na p. \<exists>nb. \<forall>nc nd pa. (\<not> (nc::nat) < nd \<or> \<not> pa (nc - nd) \<or> pa 0) \<and> (\<not> p (0::nat) \<or> p (n - na) \<or> na + nb = n)"
    by (metis (no_types) nat_diff_split)
  then have "\<not> y < ya - q \<and> \<not> y < x - q"
    using 2 1 by (metis add.commute less_diff_conv not_add_less2)
  then have "\<exists>n. (ya + n) mod q = (n + x) mod q"
    using 3 by (metis add.commute add_diff_inverse_nat less_diff_conv mod_add_left_eq)
  then show "x = ya"
    using 2 1 by (metis a add.commute)
qed

lemma surj_on_minus: assumes inj: "inj_on  (\<lambda>(b :: nat). (y + (q - b)) mod q ) {..<q}" 
shows "(\<lambda>(b :: nat). (y + (q - b)) mod q) ` {..< q} = {..< q}"
apply(rule endo_inj_surj) using inj by auto

lemma samp_uni_minus_one_time_pad: "map_spmf(\<lambda> b. (y + (q - b)) mod q) (sample_uniform q) = map_spmf id (sample_uniform q)"
using inj_on_minus surj_on_minus one_time_pad by simp
  
(*XOR theory*)

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" 
where "xor a b \<equiv> (a \<and> \<not> b) \<or> (\<not> a \<and> b)"

lemma xor_commute: "xor a b = xor b a"
by(auto simp add: xor_def)

lemma xor_assoc: "xor (xor x y) z = xor x (xor y z)"
by(auto simp add: xor_def) 

lemma xor_false_r[simp]: "xor x False = x"
by(simp add: xor_def)

lemma xor_false_l[simp]: "xor False x = x"
by(simp add: xor_def)

lemma xor_true_r[simp]: "xor x True = (\<not> x)"
by(simp add: xor_def)

lemma xor_true_l[simp]: "xor True x = (\<not> x)"
by(simp add: xor_def)

lemma xor_eq[simp]: "xor x x = False"
by(simp add: xor_def)

lemma xor_left_eq[simp]: "xor x (xor x y) = y"
by(auto simp add: xor_def)

lemma xor_not_l[simp]: "xor (\<not> x) y = (\<not> (xor x y))" 
by(auto simp add: xor_def)

lemma xor_not_r[simp]: "xor x (\<not> y) = (\<not> (xor x y))" 
by(auto simp add: xor_def)

lemma xor_l_cancel[simp]: "xor x (\<not> x) = True"
by(auto simp add: xor_def)

lemma xor_r_cancel[simp]: "xor (\<not> x) x = True"
by(auto simp add: xor_def)

lemma xor_dist_1: "(x \<and> (xor y z)) = xor (x \<and> y) (x \<and> z)"
by(auto simp add: xor_def)

lemma xor_dist_2: "((xor x y) \<and> z) = xor (x \<and> z) (y \<and> z)" 
by(auto simp add: xor_def)

lemma xor_uni_samp: "map_spmf(\<lambda> b. xor y b) (coin_spmf) = map_spmf(\<lambda> b. b) (coin_spmf)"
(is "?lhs = ?rhs")
proof-
have rhs: "?rhs = spmf_of_set {True, False}"
  by (simp add: UNIV_bool insert_commute)
also have "map_spmf(\<lambda> b. xor y b) (spmf_of_set {True, False}) = spmf_of_set((\<lambda> b. xor y b) ` {True, False})"
  by (simp add: xor_def)
also have "(\<lambda> b. xor y b) ` {True, False} = {True, False}"
  using xor_def by auto
finally show ?thesis using rhs by(simp)
qed


end