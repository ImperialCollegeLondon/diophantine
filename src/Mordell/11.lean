import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4

lemma useful_lemma (x y : ℤ)
  (p : ℕ)
  (hp : nat.prime p)
  (h8 : p ≡ 3 [MOD 4])
  (h9 : ↑p ∣ y ^ 2 + 16)
  [fact (nat.prime p)] :
  let yp : zmod p := ↑y
  in yp = ↑y → yp ^ 2 = -16 → (-16 : zmod p) / 16 = -1 :=
begin
  intros yp hyp0 hyp,
  have hpne2 : p ≠ 2,
  { unfreezingI {rintro rfl},
    delta nat.modeq at h8,
    norm_num at h8, },
  have hp : (4 : zmod p) ≠ 0,
  { intro h,
    have h2 : ((4 : ℕ) : zmod p) = 0,
      assumption_mod_cast,
    have h3 : p ∣ 4,
      exact (zmod.nat_coe_zmod_eq_zero_iff_dvd 4 p).mp h2,
    have h37 : 0 < 4 := by norm_num,
    have h4 : p ≤ 4 := nat.le_of_dvd h37 h3,
    have h5 : p = 3,
    { apply nat.modeq.eq_of_modeq_of_abs_lt h8, 
      norm_num,  
      rw abs_lt,
      norm_cast,
      split; linarith,
    }, 
    unfreezingI {subst h5},
    norm_num at h3, },
  have hi : (4^2 :  zmod p) = (16 : zmod p) := by norm_num,
  rw ← hi,
  simp [hp],
end

lemma int.exists_nat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : ∃ n : ℕ, 
  (n : ℤ) = z := 
begin
  use z.nat_abs,
  exact int.nat_abs_of_nonneg hz,
end

lemma prime_factor_congr_3_mod_4 (x : ℤ) (h : x^2 - 3*x + 9 ≡ 3 [ZMOD 4]) :
  ∃ (p : ℕ), p.prime ∧ (p : int) ∣ (x^2 - 3*x + 9)  ∧ p ≡ 3 [MOD 4] := 
begin
  have h1 : ((x^2 - 3*x + 9): ℚ) = (x - 3/2)^2 + 27/4:= by ring,
  have h2 : 0 ≤ x^2 - 3*x + 9,
  { nlinarith, },
  obtain ⟨n, hn⟩  := int.exists_nat_of_nonneg h2,
  rw ← hn at h,
  have h3 : n ≡ 3 [MOD 4],
  unfold int.modeq at h,
  unfold nat.modeq,
  assumption_mod_cast,
  obtain ⟨p, hp1, hp2, hp3⟩ := three_modulo_four_prime_factor n h3,
  refine ⟨p, hp1, _, hp3⟩,
  rwa [← hn, int.coe_nat_dvd],
end

lemma x_eq_1_zmod4 (x y : ℤ) (h : y^2 ≡ x^3 + 11 [ZMOD 4]) :
  (x ≡ 1 [ZMOD 4]) :=
begin
  change _ ≡ _ [ZMOD (4 : ℕ)] at h,
  change _ ≡ _ [ZMOD (4 : ℕ)],
  rw ← zmod.int_coe_eq_int_coe_iff at h ⊢,
  push_cast at h ⊢,
  revert h,
  generalize : (↑x : zmod 4) = xbar,
  generalize : (↑y : zmod 4) = ybar,
  intro h,
  dec_trivial!,
end

example (x y : ℤ) : y^2 ≠ x^3 + 11 :=
begin
  intro heq,
  have oddx: odd x,
    { apply int.odd_iff_not_even.2, 
      intro h, 
      rw even_iff_two_dvd at h,
      have h3: 0 < 3:= by norm_num,
      rw ← int.pow_dvd_pow_iff h3 at h,
      norm_num at h,
      rw ← int.modeq_zero_iff_dvd at h,
      have h2 := int.modeq.add_right 11 h,
      rw ← heq at h2,     
      norm_num at h2,
      have h4:= int.square_ne_three_mod_four y,
      apply h4,
      clear h4,
      have h6: (4 : ℤ ) ∣ 8:= by norm_num,
      have h5:= int.modeq.modeq_of_dvd h6 h2,
      unfold int.modeq at h5 ⊢,
      rw h5,
      norm_num,
  },
  have hxy : y^2 ≡  x^3 + 11 [ZMOD 4],
  { rw heq,},
  have hx : x ≡ 1 [ZMOD 4],
    { have htemp := x_eq_1_zmod4,
      exact htemp x y hxy,},
  have h1 := x_eq_1_zmod4,
  have h2 : y^2 + 16 ≡ (x+3)*(x^2 - 3*x + 9) [ZMOD 4],
    { rw heq,
      ring_nf,},
    have h6 : x^2 - 3*x + 9 ≡  3 [ZMOD 4],
      { have hx2 : x^2 ≡ 1 [ZMOD 4],
        { exact int.square_eq_one_mod_four_of_odd x oddx, },
        have h3x : 3*x ≡ 3 [ZMOD 4],
        { unfold int.modeq at hx ⊢,
          norm_num at hx ⊢,
          rw int.mul_mod,
          rw hx,
          norm_num,},
        have hx2px : x^2 - 3*x ≡ -2 [ZMOD 4],
        { unfold int.modeq at hx2 hx h3x ⊢,
          norm_num at hx2 h3x hx ⊢,
          rw int.sub_mod,
          rw h3x,
          rw hx2,
          norm_num,},
        unfold int.modeq at hx2 hx hx2px ⊢,
        norm_num at hx2 hx hx2px ⊢,
        rw int.add_mod,
        rw hx2px,
        norm_num,},
  obtain ⟨p, hp, hpd, h8⟩  := prime_factor_congr_3_mod_4 x h6,
  have h9 : ↑p∣y^2 + 16,
  { have h3 : y^2 + 16 = (x + 3)*(x^2 - 3*x + 9),
    { rw heq,
      ring,},
    rw h3,
    exact dvd_mul_of_dvd_right hpd (x + 3), },
  haveI : fact (nat.prime p) := ⟨hp⟩,
  set yp : zmod p := y with hyp0,
  have hyp : yp^2 = -16,
  { rw ← zmod.int_coe_zmod_eq_zero_iff_dvd at h9,
    push_cast at h9,
    linear_combination h9, },
  have hypdiv4 : (yp/4)^2 = -1,
  { norm_num,
    rw hyp,
    apply useful_lemma; try {assumption}, },
  apply zmod.mod_four_ne_three_of_sq_eq_neg_one p hypdiv4,
  rw nat.modeq at h8, 
  norm_num at h8,
  assumption,
end