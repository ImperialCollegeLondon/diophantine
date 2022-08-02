import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4

lemma int.exists_nat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : ∃ n : ℕ, 
  (n : ℤ) = z := 
begin
  use z.nat_abs,
  exact int.nat_abs_of_nonneg hz,
end

theorem modeq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] :=
int.modeq_add_fac _ int.modeq.rfl

theorem modeq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t :=
begin
  rw int.modeq_iff_dvd,
  exact exists_congr (λ t, sub_eq_iff_eq_add'),
end

lemma prime_factor_congr_3_mod_4 (x a: ℤ) (h : x^2 - a*x + a^2 ≡ 3 [ZMOD 4]) :
  ∃ (p : ℕ), p.prime ∧ (p : int) ∣ (x^2 - a*x + a^2)  ∧ p ≡ 3 [MOD 4] := 
begin
  have h1 : ((x^2 - a*x + a^2): ℚ) = (x-a/2)^2 + (3*a^2)/4:= by ring,
  have h2 : 0 ≤ x^2 - a*x + a^2,
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

example (x y n a : ℤ) (hx : n ≡ 3 [ZMOD 4]) (ha : a ≡ 2 [ZMOD 4]) (hy : n + 1 = a^3): y^2 ≠ x^3 + n :=
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
    have h2 := int.modeq.add_right n h, 
    rw ← heq at h2,
    norm_num at h2,
    apply int.square_ne_three_mod_four y,
    have h6: (4 : ℤ ) ∣ 8:= by norm_num,
    have h5:= int.modeq.modeq_of_dvd h6 h2,
    unfold int.modeq at h5 ⊢,
    rw h5,
    rw int.modeq at hx,
    exact hx, },
  have h2 : y^2+1=(x+a)*(x^2 - a*x + a^2),
  { rw heq,
    ring_nf,
    rw hy, },
  have h6 : x^2 - a*x + a^2 ≡ 3 [ZMOD 4],
  { rcases oddx with ⟨b,rfl⟩,
    ring_nf,
    symmetry,
    rcases modeq_iff_add_fac.1 ha.symm with ⟨t, rfl⟩,
    have htemp : (4 * b + (-(2 * (2 + 4 * t)) + 4)) * b + ((2 + 4 * t - 1) * 
      (2 + 4 * t) + 1) = 3 + 4 * (b^2 - 2*t*b + (4*t^2 + 3*t)),
    { ring },
    rw htemp,
    exact modeq_add_fac_self.symm, },
  obtain ⟨p, hp, hpd, hp4⟩  := prime_factor_congr_3_mod_4 x a h6,
  have h9 : ↑p∣y^2 + 1,
  { rw h2,
    exact dvd_mul_of_dvd_right hpd (x + a), },
  haveI : fact (nat.prime p) := ⟨hp⟩,
  set yp : zmod p := y with hyp0,
  have hyp : yp^2 = -1,
  { rw ← zmod.int_coe_zmod_eq_zero_iff_dvd at h9,
    push_cast at h9,
    linear_combination h9, },
  apply zmod.mod_four_ne_three_of_sq_eq_neg_one p hyp,
  rw nat.modeq at hp4, 
  norm_num at hp4,
  assumption,
end