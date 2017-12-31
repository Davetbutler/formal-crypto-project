theory Noar_Pinkas
imports Cyclic_Group_SPMF Uniform_Sampling 
begin

locale Noar_Pinkas_AND_prot_views = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes finite_group: "finite (carrier \<G>)"
  and or_gt_0: "0 < Coset.order \<G>"
  and order_q: "q = Coset.order \<G>"
  and prime_field: "a < q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a q"
begin

type_synonym 'grp' ddh_ad = "('grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> ('grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> bool spmf"

definition ddh_0 :: "'grp ddh_ad \<Rightarrow>  bool spmf"
where "ddh_0 \<A> = do {
  a \<leftarrow> sample_uniform q; 
  b \<leftarrow> sample_uniform q;
  c \<leftarrow> sample_uniform q;
  b \<leftarrow> \<A> (\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) c) (\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) (a*b));
  return_spmf b}"

definition ddh_1 :: "'grp ddh_ad \<Rightarrow>  bool spmf"
where "ddh_1 \<A> = do {
  a \<leftarrow> sample_uniform q; 
  b \<leftarrow> sample_uniform q;
  c \<leftarrow> sample_uniform q;
  b \<leftarrow> \<A> (\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) (a*b)) (\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) c);
  return_spmf b}"

definition ad_ddh :: "'grp ddh_ad \<Rightarrow> real"
where "ad_ddh \<A> = \<bar>spmf (ddh_0 \<A>) True - spmf(ddh_1 \<A>) True\<bar>"

(*The view for the case v = 0*)
definition R1_v_eq_0 :: " ('grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf"
where "R1_v_eq_0 = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  c\<^sub>1 :: nat \<leftarrow> sample_uniform q;
  return_spmf(\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) (a*b), \<^bold>g (^) c\<^sub>1)}"

(*The view for the case v = 1*)
definition R1_v_eq_1 :: "('grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf"
where "R1_v_eq_1 = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  c\<^sub>0 :: nat \<leftarrow> sample_uniform q;
  return_spmf(\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) c\<^sub>0 , \<^bold>g (^) (a*b))}"

definition S1 :: " ('grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf"
where "S1 = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  c\<^sub>1 :: nat \<leftarrow> sample_uniform q;
  let c\<^sub>0 = a*b;
  return_spmf(\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) c\<^sub>0, \<^bold>g (^) c\<^sub>1)}"

(*create the views to give to the adversary to distinguish*)
definition S1_R1_comb_outputs :: " (('grp \<times> 'grp \<times> 'grp \<times> 'grp ) \<times> ('grp \<times> 'grp \<times> 'grp \<times> 'grp )) spmf"
where "S1_R1_comb_outputs = do {
  a \<leftarrow> sample_uniform q; 
  b \<leftarrow> sample_uniform q;
  c \<leftarrow> sample_uniform q;
  return_spmf ((\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) c, \<^bold>g (^) (a*b)), (\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) (a*b), \<^bold>g (^) c))}"

definition R1_S1_comb_outputs :: " (('grp \<times> 'grp \<times> 'grp \<times> 'grp ) \<times> ('grp \<times> 'grp \<times> 'grp \<times> 'grp )) spmf"
where "R1_S1_comb_outputs = do {
  a \<leftarrow> sample_uniform q; 
  b \<leftarrow> sample_uniform q;
  c \<leftarrow> sample_uniform q;
  return_spmf ((\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) (a*b), \<^bold>g (^) c), (\<^bold>g (^) a, \<^bold>g (^) b, \<^bold>g (^) c, \<^bold>g (^) (a*b)))}"

type_synonym 'grp' dist_ad = "('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> ('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> bool spmf"

definition dist_S1_R1 :: "'grp dist_ad \<Rightarrow> bool spmf"
where "dist_S1_R1 \<A> = do {
  (a,b) \<leftarrow> S1_R1_comb_outputs; 
  \<A> a b }"

definition dist_R1_S1 :: "'grp dist_ad \<Rightarrow> bool spmf"
where "dist_R1_S1 \<A> = do { 
   (a,b) \<leftarrow> R1_S1_comb_outputs; 
  \<A> a b }"

(*4-tuple advantage*)
definition ad_dist :: "'grp dist_ad \<Rightarrow> real"
where "ad_dist \<A> = \<bar>spmf (dist_S1_R1 \<A>) True - spmf(dist_R1_S1 \<A>) True\<bar>"

text{*Definitions for party 2 security of NP*}

definition  DDH_SR :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf"
where "DDH_SR x y z = do {
  a :: nat \<leftarrow> sample_uniform (q);
  c :: nat \<leftarrow> sample_uniform (q);
  let x1 = (x*a+c) mod q;
  let x2 = (y*x1 + ((z - y*x) mod q)*a) mod q;
  return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"

definition DDH_SR_ran:: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf"
where "DDH_SR_ran x y z = do {
  x1 :: nat \<leftarrow> sample_uniform q;
  x2 \<leftarrow> sample_uniform q;
  return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"

definition DDH_SR_ran':: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf"
where "DDH_SR_ran' x y z = do {
  x1 :: nat \<leftarrow> sample_uniform q;
  return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) ((y*x1 mod q)))}"

lemma DDH_ran'_eq: assumes 1: "(z - y*x) mod q = 0" shows "DDH_SR x y z = DDH_SR_ran' x y z" 
proof-
have "DDH_SR x y z  =  do {
  a :: nat \<leftarrow> sample_uniform (q);
  x1 \<leftarrow> map_spmf (\<lambda> c. (x*a+c) mod q) (sample_uniform q);
  let x2 = (y*x1) mod q;
  return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
    by(simp add: DDH_SR_def 1 bind_map_spmf o_def Let_def)  
also have "... =  do {
  a :: nat \<leftarrow> sample_uniform (q);
  x1 \<leftarrow> sample_uniform q;
  let x2 = (y*x1) mod q;
  return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
    by(simp add: samp_uni_plus_one_time_pad)
also have "... =  do {
  x1 \<leftarrow> sample_uniform q;
  let x2 = (y*x1) mod q;
  return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
    by(simp add: bind_spmf_const order_q or_gt_0)
ultimately show ?thesis by(simp add: DDH_SR_def DDH_SR_ran'_def)
qed

lemma DDH_ran_eq: assumes 1: "0 < (z - y*x) mod q" shows "DDH_SR x y z = DDH_SR_ran x y z"
proof-
have "DDH_SR x y z = do {
    a :: nat \<leftarrow> sample_uniform (q);
    x1 \<leftarrow> map_spmf(\<lambda> c. (x*a+c) mod q) (sample_uniform q);
    let x2 = (y*x1 + ((z - y*x) mod q)*a) mod q;
    return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
      by(simp add: Let_def DDH_SR_def or_gt_0 order_q bind_spmf_const map_spmf_conv_bind_spmf)
  also have "... = do {
    a :: nat \<leftarrow> sample_uniform (q);
    x1 \<leftarrow> sample_uniform q;
    let x2 = (y*x1 + ((z - y*x)mod q)*a) mod q;
    return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
      by(simp add: samp_uni_plus_one_time_pad)
  also have "... = do {
    x1 \<leftarrow> sample_uniform q;
    x2 \<leftarrow> map_spmf(\<lambda> a. (y*x1 + ((z - y*x) mod q)*a) mod q) (sample_uniform q);
    return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
      apply(simp add: Let_def or_gt_0 order_q bind_spmf_const map_spmf_conv_bind_spmf)
      apply(rewrite bind_commute_spmf[where q="sample_uniform _"])
      by(simp)
  also have "... = do {
    x1 \<leftarrow> sample_uniform q;
    x2 \<leftarrow> map_spmf(\<lambda> a. a) (sample_uniform q);
    return_spmf(\<^bold>g, \<^bold>g (^) x1, \<^bold>g (^) y, \<^bold>g (^) x2)}"
    proof-
      have 3: "(z - y*x) mod q < q" 
        by (simp add: or_gt_0 order_q) 
      also have 2: "(z - y*x) mod q < q \<Longrightarrow> (z - y*x) mod q \<noteq> 0 \<Longrightarrow> coprime ((z - y*x) mod q) q"
        using prime_field 1 by simp
      then have "coprime ((z - y*x) mod q) q" using 2 1 3 prime_field 
        by simp
      ultimately show ?thesis by(simp add: add_mult_one_time_pad)
    qed
ultimately show ?thesis by(simp add: DDH_SR_def DDH_SR_ran_def)
qed

definition S2 :: "bool \<Rightarrow> (bool \<times> nat \<times> nat \<times> nat \<times> nat \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
where "S2 v  = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (0 < (c\<^sub>v' - b*a) mod q);
  x1 \<leftarrow> sample_uniform q;
  x2 \<leftarrow> sample_uniform q;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, \<^bold>g (^) x1,  \<^bold>g (^) b,  \<^bold>g (^) x2)}"

definition R2 :: "'grp \<Rightarrow> 'grp \<Rightarrow> bool \<Rightarrow> (bool \<times> nat \<times> nat \<times> nat \<times> nat \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
where "R2 m0 m1 v  = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 <(c\<^sub>v' - b*a) mod q);
  (g, x, y\<^sub>0, z\<^sub>0') \<leftarrow> DDH_SR a b c\<^sub>v;
  (g, x, y\<^sub>1, z\<^sub>1') \<leftarrow> DDH_SR a b c\<^sub>v';
  let enc_m0 = z\<^sub>0' \<otimes> m0;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', y\<^sub>0, enc_m0, y\<^sub>1, enc_m1)}" 

definition R2_DDH_SR_ran :: "'grp \<Rightarrow> 'grp \<Rightarrow> bool \<Rightarrow> (bool \<times> nat \<times> nat \<times> nat \<times> nat \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
where "R2_DDH_SR_ran m0 m1 v  = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (0 < (c\<^sub>v' - b*a) mod q);
  (g, x, y\<^sub>0, z\<^sub>0') \<leftarrow> DDH_SR_ran' a b c\<^sub>v;
  (g, x, y\<^sub>1, z\<^sub>1') \<leftarrow> DDH_SR_ran a b c\<^sub>v';
  let enc_m0 = z\<^sub>0' \<otimes> m0;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', y\<^sub>0, enc_m0, y\<^sub>1, enc_m1)}" 

lemma R2_eq_R2_DDH_SR_ran: "R2 m0 m1 v = R2_DDH_SR_ran m0 m1 v" 
proof-
have "R2 m0 m1 v = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  (g, x, y\<^sub>0, z\<^sub>0') \<leftarrow> DDH_SR_ran' a b c\<^sub>v;
  (g, x, y\<^sub>1, z\<^sub>1') \<leftarrow> DDH_SR_ran a b c\<^sub>v';
  let enc_m0 = z\<^sub>0' \<otimes> m0;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', y\<^sub>0, enc_m0, y\<^sub>1, enc_m1)}"
    by(simp add: R2_def DDH_ran'_eq DDH_ran_eq order_q cong: bind_spmf_cong_simp)
then show ?thesis by(simp add: R2_def R2_DDH_SR_ran_def)
qed

end

locale proofs = Noar_Pinkas_AND_prot_views + cyclic_group \<G>
begin

lemma inf_theoretic_P2: assumes 1: "m0 \<in> carrier \<G>" and 2: "m1 \<in> carrier \<G>" shows "R2 m0 m1 v = S2 v"
proof-
have "R2_DDH_SR_ran m0 m1 v  = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  x1 \<leftarrow> sample_uniform q;
  let z\<^sub>0' =  \<^bold>g (^) (b*x1 mod q);
  x2 :: nat  \<leftarrow> sample_uniform q;
  x3 \<leftarrow> sample_uniform q;
  let z\<^sub>1' =  \<^bold>g (^) x3;
  let enc_m0 = z\<^sub>0' \<otimes> m0;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    by(simp add: Let_def DDH_SR_ran'_def DDH_SR_ran_def R2_DDH_SR_ran_def)
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  t \<leftarrow> map_spmf (\<lambda> x1. (b*x1 mod q)) (sample_uniform q) ;
  let z\<^sub>0' =  \<^bold>g (^) t;
  x2 :: nat  \<leftarrow> sample_uniform q;
  x3 :: nat \<leftarrow> sample_uniform q;
  let z\<^sub>1' =  \<^bold>g (^) x3;
  let enc_m0 = z\<^sub>0' \<otimes> m0;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    by(simp add: bind_map_spmf o_def)
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  t \<leftarrow> (sample_uniform q) ;
  let z\<^sub>0' =  \<^bold>g (^) t;
  x2 :: nat  \<leftarrow> sample_uniform q;
  x3 :: nat \<leftarrow> sample_uniform q;
  let z\<^sub>1' =  \<^bold>g (^) x3;
  let enc_m0 = z\<^sub>0' \<otimes> m0;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    by(clarsimp simp add: mult_one_time_pad Let_def cong: bind_spmf_cong_simp) 
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  enc_m0 \<leftarrow> map_spmf (\<lambda>t. \<^bold>g (^) t \<otimes> m0) (sample_uniform q);
  x2 :: nat  \<leftarrow> sample_uniform q;
  x3 :: nat \<leftarrow> sample_uniform q;
  let z\<^sub>1' =  \<^bold>g (^) x3;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    by(simp add: bind_map_spmf o_def)
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  enc_m0 \<leftarrow> map_spmf (\<lambda>t. \<^bold>g (^) t ) (sample_uniform q);
  x2 :: nat  \<leftarrow> sample_uniform q;
  x3 :: nat \<leftarrow> sample_uniform q;
  let z\<^sub>1' =  \<^bold>g (^) x3;
  let enc_m1 = z\<^sub>1' \<otimes> m1;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    using 1 by(simp add: sample_uniform_one_time_pad order_q)
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  t \<leftarrow> sample_uniform q;
  let enc_m0  =  \<^bold>g (^) t;
  x2 :: nat  \<leftarrow> sample_uniform q;
  enc_m1 \<leftarrow> map_spmf (\<lambda> x3. \<^bold>g (^) x3 \<otimes> m1) (sample_uniform q);
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    by(simp add: bind_map_spmf o_def)
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  t \<leftarrow> sample_uniform (Coset.order \<G>);
  let enc_m0  =  \<^bold>g (^) t;
  x2 :: nat  \<leftarrow> sample_uniform q;
  enc_m1 \<leftarrow> map_spmf (\<lambda> x3. \<^bold>g (^) x3) (sample_uniform q);
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    using 2 by(simp add: sample_uniform_one_time_pad order_q)
also have "... = do {
  a :: nat \<leftarrow> sample_uniform q;
  b :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf (coprime b q);
  let c\<^sub>v = a*b;
  c\<^sub>v' :: nat \<leftarrow> sample_uniform q;
  _ :: unit \<leftarrow> assert_spmf ( 0 < (c\<^sub>v' - b*a) mod q);
  t \<leftarrow> sample_uniform q;
  let enc_m0  =  \<^bold>g (^) t;
  x3 \<leftarrow> sample_uniform q;
  let enc_m1 =  \<^bold>g (^) x3;
  return_spmf(v, a, b, c\<^sub>v, c\<^sub>v', \<^bold>g (^) b, enc_m0,  \<^bold>g (^) b, enc_m1)}" 
    by(simp add: bind_map_spmf o_def or_gt_0 bind_spmf_const order_q)
ultimately show ?thesis by(simp add: S2_def R2_eq_R2_DDH_SR_ran)
qed

(*Security for the case for v = 0*)
lemma sec_S1_R1_v_eq_0: "R1_v_eq_0 = S1"
by(simp add: R1_v_eq_0_def S1_def)

(*case v=1 -reduce to DDH assumption*)
type_synonym 'grp' adversary = "('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> ('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> bool spmf" 

(*The adversary we use to 'break' the DDH assumption*)
fun A :: "'grp adversary \<Rightarrow> ('grp \<times> 'grp \<times> 'grp) \<Rightarrow> ('grp \<times> 'grp \<times> 'grp) \<Rightarrow> bool spmf"
where "A \<A> (a0, b0, c0) (a1, b1, c1) = do {
  b \<leftarrow> \<A> (a0, b0, c0, c1) (a1, b1, c1, c0);
  return_spmf(b)}"

lemma sec_sender: "ad_ddh (A \<A>) = ad_dist \<A>"
unfolding ad_ddh_def ad_dist_def ddh_0_def ddh_1_def dist_R1_S1_def dist_S1_R1_def S1_def R1_v_eq_1_def S1_R1_comb_outputs_def R1_S1_comb_outputs_def
by(simp)

end
end

