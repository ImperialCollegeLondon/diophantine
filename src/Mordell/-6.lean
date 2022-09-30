import tactic
import data.int.parity
import data.int.modeq
import data.nat.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4


lemma mod_8_of_factors_17 {n : ℕ} (hn: n ≥ 1) (hfac : ∀ p ∈ n.factors, p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8]) :
  n ≡ 1 [MOD 8] ∨ n ≡ 7 [MOD 8] :=
begin
  induction n using nat.rec_on_mul with p hp a b ha hb,
  { linarith },
  { left, refl },
  { rw nat.factors_prime hp at hfac,
    exact hfac p (list.mem_cons_self p list.nil) },
  { by_cases ha2 : a = 0,
    { nlinarith },
    by_cases hb2 : b = 0,
    { nlinarith },
    { have key_a : ∀ p ∈ a.factors, p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8] :=
        (λ p hp, hfac p (nat.mem_factors_mul_left hp hb2)),
      have key_b : ∀ p ∈ b.factors, p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8] :=
        (λ p hp, hfac p (nat.mem_factors_mul_right hp ha2)),
      cases ha (by nlinarith) key_a with a_8 a_8;
      cases hb (by nlinarith) key_b with b_8 b_8,
      { left, have : a * b ≡ 1 * 1 [MOD 8] := nat.modeq.mul a_8 b_8, assumption },
      { right, have : a * b ≡ 1 * 7 [MOD 8] := nat.modeq.mul a_8 b_8, assumption },
      { right, have : a * b ≡ 7 * 1 [MOD 8] := nat.modeq.mul a_8 b_8, assumption },
      { left, have : a * b ≡ 7 * 7 [MOD 8] := nat.modeq.mul a_8 b_8, assumption },
    },
  },
end

lemma mod_8_of_mod {n : ℕ} (n_odd : odd n) :  ¬( n ≡ 3 [MOD 8] ∨ n ≡ 5 [MOD 8]) ↔ (n ≡ 1 [MOD 8] ∨ n ≡ 7 [MOD 8]) :=
begin
  push_neg,
  split,
  swap,
  { intro h17,
    cases h17 with h h; split;
    { unfold nat.modeq at h ⊢, rw h, norm_num, }, },
  { rintro ⟨hn3_8, hn5_8⟩,
    have n_odd' : n % 2 = 1,
    { rcases n_odd with ⟨k, rfl⟩,
      rw add_comm,
      norm_num, },
    cases nat.odd_mod_four_iff.mp n_odd' with h1_4 h3_4,
    { left,
      obtain ⟨k, hk⟩ : (4 : ℤ) ∣ 1-n := nat.modeq.dvd h1_4,
      rw nat.modeq_iff_dvd at hn5_8 ⊢,
      norm_num at hn5_8 ⊢,
      rw hk,
      rcases int.even_or_odd' k with ⟨l, rfl | rfl⟩,
      { ring_nf,
        norm_num, },
      { have key : 5 - ↑n = 8*(l+1) := by linarith,
        rw key at hn5_8,
        exfalso,
        norm_num at hn5_8, },
    },
    { right,
      have H : (4 : ℤ) ∣ 7-n := nat.modeq.dvd h3_4,
      cases H with k hk,
      rw nat.modeq_iff_dvd at hn3_8 ⊢,
      norm_num at hn3_8 ⊢,
      rw hk,
      rcases int.even_or_odd' k with ⟨l, rfl | rfl⟩,
      { ring_nf,
        norm_num, },
      { have key : 3 - ↑n = 8*l := by linarith,
        rw key at hn3_8,
        exfalso,
        norm_num at hn3_8, }, }, },
end

lemma prime_factor_congr_3_mod_4 {n : ℤ} (hn_8 : n ≡ 3 [ZMOD 8] ∨ n ≡ 5 [ZMOD 8]) :
  ∃ (p : ℕ), p.prime ∧ (p : int) ∣ n  ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5  [MOD 8]) := 
begin
  by_contradiction hdiv,
  push_neg at hdiv,
  have n_odd : odd n,
  { cases hn_8 with hn_8 hn_8;
    exact int.odd_iff.mpr (int.modeq.modeq_of_dvd (by norm_num : (2 : ℤ) ∣ 8) hn_8), },
  let N : ℕ := n.nat_abs,
  have N_odd : odd N := int.nat_abs_odd.mpr n_odd,
  have hfac : ∀ p ∈ N.factors, p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8],
  { intros p hp,
    have p_div_N := nat.dvd_of_mem_factors hp,
    have p_odd : odd p,
    { cases p_div_N with k hk,
      rw hk at N_odd,
      apply nat.odd.of_mul_left N_odd, },
    apply (mod_8_of_mod p_odd).mp,
    push_neg,
    apply hdiv p (nat.prime_of_mem_factors hp),
    exact int.coe_nat_dvd_left.mpr p_div_N, },
  have N_ne_0 : N ≠ 0 := nat.ne_of_odd_add N_odd,
  have key := mod_8_of_factors_17 (nat.one_le_iff_ne_zero.mpr N_ne_0) hfac,
  apply (mod_8_of_mod N_odd).mpr key,
  rw [← int.coe_nat_modeq_iff, ← int.coe_nat_modeq_iff],
  by_cases n_pos : 0 ≤ n,
  { rw int.nat_abs_of_nonneg n_pos,
    exact hn_8, },
  { have hNn : ↑N = -n := int.of_nat_nat_abs_of_nonpos (by linarith),
    rw hNn,
    cases hn_8 with hn3_8 hn5_8,
    { right,
      apply int.modeq.add_left_cancel hn3_8,
      norm_num,
      refl, },
    { left,
      apply int.modeq.add_left_cancel hn5_8,
      norm_num,
      refl, },
  },
end

example (x y : ℤ) : y^2 ≠ x^3 - 6 :=
begin
  intro heq,
  have oddx: odd x,
  { by_contradiction evenx,
    rw ← int.even_iff_not_odd at evenx,
    rw even_iff_two_dvd at evenx,
    have hy2 : y^2 ≡ 2 [ZMOD 8],
    { rw heq,
      rcases evenx with ⟨k, rfl⟩,
      apply int.modeq_of_dvd,
      exact dvd.intro (1-k^3) (by ring),
    },
    replace hy2 := int.modeq.modeq_of_dvd (by norm_num : (4:ℤ)∣8) hy2,
    exact int.square_ne_two_mod_four y hy2,
  },
  have oddy: odd y,
  { rw [int.odd_iff_not_even, ← int.even_pow' (by norm_num : 2≠0), ← int.odd_iff_not_even, heq],
    rcases oddx with ⟨k, rfl⟩,
    refine ⟨(((4*k+6)*k+3)*k-3), _⟩,
    ring
  },
  have x_8 : x ≡ 7 [ZMOD 8],
  { have heq' : x^3 = y^2 + 6 := by linarith,
    have x3_8 : x^3 ≡ 7 [ZMOD 8],
    { rw heq',
      rcases oddy with ⟨k, rfl⟩,
      apply int.modeq_of_dvd,
      ring_nf,
      rw (by ring : (-(4*k)-4)*k = -4*(k*(k+1))),
      cases int.even_mul_succ_self k with m hm,
      rw hm,
      exact dvd.intro (-m) (by ring),
    },
    have x2_8 : x^2 ≡ 1 [ZMOD 8],
    { rcases oddx with ⟨k, rfl⟩,
      cases int.even_mul_succ_self k with m hm,
      calc ((2*k + 1)^2) % 8 = (4*(k*(k+1)) + 1) % 8 : by ring_nf
                         ... = (4*(m+m) + 1) % 8     : by rw hm
                         ... = (1 + 8*m) % 8         : by ring_nf
                         ... = 1                     : int.modeq_add_fac_self,
    },
    calc x % 8 = x * 1 % 8   : by ring_nf
           ... = x * x^2 % 8 : (int.modeq.mul_left x x2_8).symm
           ... = x^3 % 8     : by ring_nf
           ... = 7           : x3_8,
  },
  have h2 : y^2 - 2 = (x-2)*(x^2 + 2*x + 4),
  { rw heq,
    ring, },
  have H : x^2 + 2*x + 4 ≡ 3 [ZMOD 8],
  { obtain ⟨k, hk⟩ := int.modeq.dvd x_8,
    replace hk : x = 7 - 8*k := by linarith,
    rw [hk, int.modeq_iff_dvd],
    exact dvd.intro ((16 - k * 8) * k - 8) (by ring), },
  rcases prime_factor_congr_3_mod_4 (or.inl H) with ⟨p, p_prime, p_div, p35_8⟩,
  have y22_p : y^2 ≡ 2 [ZMOD p],
  { symmetry,
    apply int.modeq_iff_dvd.mpr,
    rw h2,
    exact dvd_mul_of_dvd_right p_div (x - 2), },
  have sq2_p : is_square (2 : zmod p),
  { apply is_square_of_exists_sq (2 : zmod p),
    refine ⟨y, _⟩,
    have key := (zmod.int_coe_eq_int_coe_iff 2 (y^2) p).mpr y22_p.symm,
    norm_num at key,
    exact key, },
  have p_ne_2 : p ≠ 2,
  { rintro rfl,
    cases p35_8 with p35_8 p35_8;
    rw nat.modeq_iff_dvd at p35_8;
    norm_num at p35_8, },
  haveI K : fact (nat.prime p) := {out := p_prime},
  have p17_8 := (zmod.exists_sq_eq_two_iff p_ne_2).mp sq2_p,
  exact (mod_8_of_mod (nat.prime.odd p_prime p_ne_2)).mpr p17_8 p35_8,
end
