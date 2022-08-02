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

lemma do_we_have (x a: ℤ) (h : x^2 - a*x + a^2 ≡ 3 [ZMOD 4]) :
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

example (x y n a : ℤ) (h : -1 < n) (hx : n ≡ 3 [ZMOD 4]) (ha : a ≡ 2 [ZMOD 4]) (hy : n + 1 = a^3): y^2 ≠ x^3 + n :=
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
    sorry, },
  have h7 : ((x^2 - a*x + a^2): ℚ) = (x-a/2)^2 + (3*a^2)/4:= by ring,
  sorry,
end