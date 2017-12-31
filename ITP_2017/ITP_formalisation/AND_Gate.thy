theory AND_Gate
imports Uniform_Sampling 
begin 

definition A :: "bool \<Rightarrow> (bool \<times> bool) spmf"
where "A e = do {
  r0 :: bool \<leftarrow> coin_spmf;
  r1 \<leftarrow> coin_spmf;
  let re = (if e then r1 else r0);
  let re' = (if e then r0 else r1);
  return_spmf (re, re')}"

definition A' :: "bool \<Rightarrow> (bool \<times> bool) spmf"
where "A' e = do {
  r0 :: bool \<leftarrow> coin_spmf;
  r1 :: bool \<leftarrow> coin_spmf;
  return_spmf (r0, r1)}"

lemma A_eq_A': "A e = A' e"
proof(cases e)
case True 
have "A e = do {
  r0 :: bool \<leftarrow> coin_spmf;
  r1 \<leftarrow> coin_spmf;
  return_spmf (r1, r0)}"
using True by(simp add: A_def)
also have "... = do {
   r0 :: bool \<leftarrow> coin_spmf;
  r1 \<leftarrow> coin_spmf;
  return_spmf (r0, r1)}"
    apply(rewrite bind_commute_spmf [where p="coin_spmf"]) by(simp)
    ultimately show ?thesis by(simp add: A'_def)
next case False
show ?thesis using False by(simp add: A_def A'_def)
qed

(*OT (with trusted initialiser) to be used in AND gate protocol*)
definition Trusted :: "(bool \<times> bool \<times> bool \<times> bool) spmf"
where "Trusted = do {
  d \<leftarrow> coin_spmf;
  r0 :: bool \<leftarrow> coin_spmf;
  r1 \<leftarrow> coin_spmf;
  return_spmf (r0, r1, d, if d then r1 else r0)}"

definition R\<^sub>1 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> bool spmf"
where "R\<^sub>1 msg c = do {
  let (m0, m1) = msg;
  (r0, r1, d, rd) \<leftarrow> Trusted;
  let e = xor c d;
  return_spmf e}"

definition S\<^sub>1 :: "(bool \<times> bool) \<Rightarrow> bool spmf"
where "S\<^sub>1 msg = do {
  e' :: bool \<leftarrow> coin_spmf;
  return_spmf e'}"

lemma OT_sec_P\<^sub>1: "R\<^sub>1 msg c = S\<^sub>1 msg"
proof-
have "R\<^sub>1 msg c = do {
  let (m0, m1) = msg;
  d :: bool \<leftarrow> coin_spmf;
  r0 :: bool \<leftarrow> coin_spmf;
  r1 :: bool \<leftarrow> coin_spmf;
  let e = xor c d;
  return_spmf e}"
    by(simp add: R\<^sub>1_def Trusted_def)
also have "... = do {
  let (m0, m1) = msg;
  r0 :: bool \<leftarrow> coin_spmf;
  r1 :: bool \<leftarrow> coin_spmf;
  e \<leftarrow> map_spmf (\<lambda> d. xor c d) (coin_spmf);
  return_spmf e}"
    by(simp add: bind_spmf_const map_spmf_conv_bind_spmf)
also have "... = do {
  r0 :: bool \<leftarrow> coin_spmf;
  r1 :: bool \<leftarrow> coin_spmf;
  e \<leftarrow> (coin_spmf);
  return_spmf e}"
    by(simp add: xor_uni_samp)
ultimately show ?thesis by(simp add: S\<^sub>1_def bind_spmf_const)
qed

definition R\<^sub>2 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) spmf"
where "R\<^sub>2 msg c = do {
  let (m0, m1) = msg;
  (r0, r1, d, rd) \<leftarrow> Trusted;
  let e = xor c d;
  let re = (if e then r1 else r0);
  let re' = (if e then r0 else r1);
  let f0 = xor m0 re;
  let f1 = xor m1 re';
  return_spmf (f0, f1) }"

definition S\<^sub>2 :: "bool \<Rightarrow> (bool \<times> bool) spmf"
where "S\<^sub>2 c = do {
  r0 \<leftarrow> coin_spmf;
  r1 :: bool \<leftarrow> coin_spmf;
  return_spmf (r0, r1)}"

lemma OT_sec_P\<^sub>2: "R\<^sub>2 msg c = S\<^sub>2 c"
proof-
have "R\<^sub>2 msg c = do {
  let (m0, m1) = msg;
  e \<leftarrow> map_spmf (\<lambda> d. xor c d) coin_spmf;
  r0 \<leftarrow> coin_spmf;
  r1 \<leftarrow> coin_spmf;
  let re = (if e then r1 else r0);
  let re' = (if e then r0 else r1);
  let f0 = xor m0 re;
  let f1 = xor m1 re';
  return_spmf (f0, f1) }"
    by(simp add: R\<^sub>2_def Trusted_def bind_spmf_const map_spmf_conv_bind_spmf Let_def)
also have "... = do {
  let (m0, m1) = msg;
  e \<leftarrow> coin_spmf;
  (re, re') \<leftarrow> A e;
  let f0 = xor m0 re;
  let f1 = xor m1 re';
  return_spmf (f0, f1) }" 
    by(simp add: A_def xor_uni_samp) 
also have "... = do {
   let (m0, m1) = msg;
  e \<leftarrow> coin_spmf;
  (re, re') \<leftarrow> A' e;
  let f0 = xor m0 re;
  let f1 = xor m1 re';
  return_spmf (f0, f1) }" 
    by(simp add: A_eq_A') 
also have "... = do {
  let (m0, m1) = msg;
  e :: bool \<leftarrow> coin_spmf;
  re :: bool \<leftarrow> coin_spmf;
  re' :: bool \<leftarrow> coin_spmf;
  let f0 = xor m0 re;
  let f1 = xor m1 re';
  return_spmf (f0, f1) }"
    by(simp add: A'_def)
also have "... = do {
  let (m0, m1) = msg;
  f0 :: bool \<leftarrow> map_spmf (\<lambda> re.  xor m0 re) coin_spmf;
  f1 \<leftarrow> map_spmf (\<lambda> re'. xor m1 re') coin_spmf;
  return_spmf (f0, f1) }"
    by(simp add: bind_spmf_const map_spmf_conv_bind_spmf Let_def)
also have "... = do {
  f0 :: bool \<leftarrow> coin_spmf;
  f1 \<leftarrow> coin_spmf;
  return_spmf (f0, f1) }"
    by(simp add: xor_uni_samp)
ultimately show ?thesis by(simp add: S\<^sub>2_def)
qed

(*AND gate security*)

definition R\<^sub>a :: "bool \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) spmf"
where "R\<^sub>a a b = do {
  u \<leftarrow> coin_spmf;
  let m0 = \<not> u;
  let m1 = xor a (\<not> u);
  r \<leftarrow> R\<^sub>1 (m0,m1) b;
  return_spmf (u, r)}"

definition S\<^sub>a :: "bool \<Rightarrow> (bool \<times> bool) spmf"
where "S\<^sub>a a = do {
  u \<leftarrow> coin_spmf;
  let m0 = \<not> u;
  let m1 = xor a (\<not> u);
  r \<leftarrow> S\<^sub>1 (m0, m1);
  return_spmf (u, r)}"

lemma AND_sec\<^sub>a: "R\<^sub>a a b = S\<^sub>a a"
by(simp add: OT_sec_P\<^sub>1 R\<^sub>a_def S\<^sub>a_def)

definition R\<^sub>b :: "bool \<Rightarrow> bool \<Rightarrow> (bool \<times> bool \<times> bool) spmf"
where "R\<^sub>b a b = do {
  u :: bool \<leftarrow> coin_spmf;
  let m0 = \<not> u;
  let m1 = xor a (\<not> u);
  r \<leftarrow> R\<^sub>2 (m0, m1) b;
  return_spmf (b,r)}"

definition S\<^sub>b :: "bool \<Rightarrow> (bool \<times> bool \<times> bool) spmf"
where "S\<^sub>b b = do {
  r \<leftarrow> S\<^sub>2 b;
  return_spmf (b,r)}"

lemma AND_sec\<^sub>b: "R\<^sub>b a b = S\<^sub>b b"
by(simp add: OT_sec_P\<^sub>2 R\<^sub>b_def S\<^sub>b_def bind_spmf_const)

end