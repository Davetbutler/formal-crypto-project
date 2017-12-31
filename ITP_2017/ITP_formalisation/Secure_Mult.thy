theory Secure_Mult
imports Cyclic_Group_SPMF Uniform_Sampling Comp_Indist
begin

(*Here we prove information theoretic security for the secure multiplication protocol*)

lemma weight_1: assumes 1: "q > 0" shows "lossless_spmf (sample_uniform q)"
apply(auto simp add: sample_uniform_def) 
using assms by blast

(*Security for party 1*)

(*Construct views of pary 1*)
definition R1 :: "(nat \<times> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) spmf"
where "R1 input n = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> sample_uniform q;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(x mod q, a, r, (y + (q - b)) mod q, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"

definition  S1 :: "(nat \<times> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) spmf"
where "S1 input n = do {
  let (x,y) = input;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  c' \<leftarrow> sample_uniform q;
  s1' \<leftarrow> sample_uniform q;
  return_spmf(x mod nat q, a', (x*b' + (q -c')) mod q, b', s1', (x*y mod q - s1') mod q)}"

(*Security is information theoretic*)
lemma inf_theoretic_1: assumes 1: "q > 0" shows "R1 input n = S1 input n"
proof-
have "R1 input n = do {
  let (x,y) = input;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  c' \<leftarrow> sample_uniform q;
  s1' \<leftarrow> sample_uniform q;
  return_spmf(x mod nat q, a', c', b', s1', (x*y mod q - s1') mod q)}"
    proof-
    have "R1 input n = do {
      let (x,y) = input;
      a :: nat \<leftarrow> sample_uniform q;  
      b \<leftarrow> map_spmf(\<lambda> b.  (y + (q - b)) mod q) (sample_uniform q);
      r :: nat \<leftarrow> sample_uniform q;
      a' :: nat \<leftarrow> sample_uniform q;
      b' :: nat \<leftarrow> sample_uniform q;
      r' :: nat \<leftarrow> sample_uniform q;
      return_spmf(x mod q, a, r, b, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
        by(simp add: R1_def map_spmf_conv_bind_spmf bind_spmf_const)
    also have "... = do {
      let (x,y) = input;
      a :: nat \<leftarrow> sample_uniform q;  
      b \<leftarrow> map_spmf(\<lambda> b. b) (sample_uniform q);
      r :: nat \<leftarrow> sample_uniform q;
      a' :: nat \<leftarrow> sample_uniform q;
      b' :: nat \<leftarrow> sample_uniform q;
      r' :: nat \<leftarrow> sample_uniform q;
      return_spmf(x mod q, a, r, b, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
        by(simp add: samp_uni_minus_one_time_pad)
    also have "... = do {
      let (x,y) = input;
      a :: nat \<leftarrow> sample_uniform q;  
      b \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      a' :: nat \<leftarrow> sample_uniform q;
      b' :: nat \<leftarrow> sample_uniform q;
      r' :: nat \<leftarrow> sample_uniform q;
      return_spmf(x mod q, a, r, b, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
        by(simp)
    also have "... = do {
      let (x,y) = input;
      a :: nat \<leftarrow> sample_uniform q;  
      b \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      a' :: nat \<leftarrow> sample_uniform q;
      b' :: nat \<leftarrow> sample_uniform q;
      z \<leftarrow> map_spmf(\<lambda> r'.  (x*(y-b') + (q - r')) mod q) (sample_uniform q);
      return_spmf(x mod q, a, r, b, z, ((x*y mod q - z) mod q))}"
        by(simp add: map_spmf_conv_bind_spmf bind_spmf_const)
    also have "... = do {
      let (x,y) = input;
      a :: nat \<leftarrow> sample_uniform q;  
      b \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      a' :: nat \<leftarrow> sample_uniform q;
      b' :: nat \<leftarrow> sample_uniform q;
      z \<leftarrow> map_spmf(\<lambda> r'.  r') (sample_uniform q);
      return_spmf(x mod q, a, r, b, z, ((x*y mod q - z) mod q))}"
        by(simp add: samp_uni_minus_one_time_pad)
    also have "... = do {
      let (x,y) = input;
      a :: nat \<leftarrow> sample_uniform q;  
      b \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      z \<leftarrow> sample_uniform q;
      return_spmf(x mod q, a, r, b, z, ((x*y mod q - z) mod q))}"
        by(simp add: weight_1 1 bind_spmf_const)
    ultimately show ?thesis by(simp add: R1_def S1_def)
  qed
also have "S1 input n = do {
  let (x,y) = input;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  c' \<leftarrow> sample_uniform q;
  s1' \<leftarrow> sample_uniform q;
  return_spmf(x mod nat q, a', c', b', s1', (x*y mod q - s1') mod q)}"
  proof-
  have "S1 input n = do {
    let (x,y) = input;
    a' :: nat \<leftarrow> sample_uniform q;
    b' :: nat \<leftarrow> sample_uniform q;
    z \<leftarrow> map_spmf(\<lambda> c'. (x*b' + (q -c')) mod q) (sample_uniform q);
    s1' \<leftarrow> sample_uniform q;
    return_spmf(x mod nat q, a', z, b', s1', (x*y mod q - s1') mod q)}"
      by(simp add: S1_def map_spmf_conv_bind_spmf bind_spmf_const)
  also have "... = do {
    let (x,y) = input;
    a' :: nat \<leftarrow> sample_uniform q;
    b' :: nat \<leftarrow> sample_uniform q;
    z \<leftarrow> map_spmf(\<lambda> c'. c') (sample_uniform q);
    s1' \<leftarrow> sample_uniform q;
    return_spmf(x mod nat q, a', z, b', s1', (x*y mod q - s1') mod q)}"
      by(simp add: samp_uni_minus_one_time_pad)
  ultimately show ?thesis by(simp)
  qed
ultimately show ?thesis by(simp add: S1_def R1_def)
qed


lemma comp_indist_sec_1: assumes "q > 0" shows "comp_indist (R1) (S1)"
using inf_theoretic_1 assms unfolding comp_indist_def
by auto

(*Security for party 2*)

(*Construct views*)
definition R2 :: "(nat \<times> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) spmf"
where "R2 input n = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> sample_uniform q;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, (a*b  + (q - r)) mod q, (x + a) mod q, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"

definition  S2 :: "(nat \<times> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) spmf"
where "S2 input n = do {
  let (x,y) = input;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  c' :: nat \<leftarrow> sample_uniform q;
  s1' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b', c', a', s1', (x*y mod q - s1') mod q)}"

(*Security is information theoretic*)
lemma inf_theoretic_2: assumes 1: "q > 0" shows "R2 input n = S2 input n"
proof- 
have "R2 input n = do {
  let (x,y) = input;   a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r \<leftarrow> map_spmf (\<lambda> r. (a*b  + (q - r)) mod q) (sample_uniform q);
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, (x + a) mod q, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
    by(simp add: R2_def map_spmf_conv_bind_spmf bind_spmf_const)
also have "... = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r \<leftarrow> map_spmf (\<lambda> r. r) (sample_uniform q);
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, (x + a) mod q, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
    by(simp add: samp_uni_minus_one_time_pad)  
also have "... = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r ::nat \<leftarrow> (sample_uniform q);
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, (x + a) mod q, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
    by(simp)
also have "... = do {
  let (x,y) = input;
  a \<leftarrow> map_spmf(\<lambda> a. (x + a) mod q) (sample_uniform q);  
  b :: nat \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> (sample_uniform q);
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, a, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
    by(simp add:map_spmf_conv_bind_spmf bind_spmf_const)
also have "... = do {
  let (x,y) = input;
  a \<leftarrow> map_spmf(\<lambda> a. a) (sample_uniform q);  
  b :: nat \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> (sample_uniform q);
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, a, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
    by(simp add: samp_uni_plus_one_time_pad) 
also have "... = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> sample_uniform q;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  r' :: nat \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, a, (x*(y-b') + (q - r')) mod q, ((x*y mod q - (x*(y-b') + (q - r')) mod q) mod q))}"
    by(simp)
also have "... = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b :: nat \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> sample_uniform q;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  z \<leftarrow> map_spmf(\<lambda> r'.  (x*(y-b') + (q - r')) mod q) (sample_uniform q);
  return_spmf(y mod q, b, r, a, z, ((x*y mod q - z) mod q))}"
    by(simp add: map_spmf_conv_bind_spmf bind_spmf_const)
also have "... = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> sample_uniform q;
  a' :: nat \<leftarrow> sample_uniform q;
  b' :: nat \<leftarrow> sample_uniform q;
  z \<leftarrow> map_spmf(\<lambda> r'.  r') (sample_uniform q);
  return_spmf(y mod q, b, r, a, z, ((x*y mod q - z) mod q))}"
    by(simp add: samp_uni_minus_one_time_pad)
also have "... = do {
  let (x,y) = input;
  a :: nat \<leftarrow> sample_uniform q;  
  b \<leftarrow> sample_uniform q;
  r :: nat \<leftarrow> sample_uniform q;
  z \<leftarrow> sample_uniform q;
  return_spmf(y mod q, b, r, a, z, ((x*y mod q - z) mod q))}"
    by(simp add: weight_1 1 bind_spmf_const)
ultimately show ?thesis by(simp add: R2_def S2_def) 
qed

lemma comp_indist_sec_2: assumes "q > 0" shows "comp_indist (R2) (S2)"
using inf_theoretic_2 assms unfolding comp_indist_def
by auto


end
