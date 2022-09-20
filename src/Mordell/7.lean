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

lemma do_we_have (x : ℤ) (h : x^2 - 2*x + 4 ≡ 3 [ZMOD 4]) :
  ∃ (p : ℕ), p.prime ∧ (p : int) ∣ (x^2 - 2*x + 4)  ∧ p ≡ 3 [MOD 4] := 
begin
  have h1 : (x^2 - 2*x + 4) = (x-1)^2 + 3:= by ring,
  have h2 : 0 ≤ x^2 - 2*x + 4,
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

example (x y : ℤ) : y^2 ≠ x^3 + 7 :=
begin
  intro heq,
  have oddx: odd x,
    { apply int.odd_iff_not_even.2, 
      intro h, 
      rw even_iff_two_dvd at h,
      have h3: 0 < 3,
        {
          norm_num,
        },
      rw ← int.pow_dvd_pow_iff h3 at h,
      norm_num at h,
      rw ← int.modeq_zero_iff_dvd at h,
      have h2 := int.modeq.add_right 7 h,
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
  have h2 : y^2+1=(x+2)*(x^2 - 2*x + 4),
    { rw heq,
      ring,
    },
  have h6 : (x-1)^2 + 3 ≡  3 [ZMOD 4],
    { rcases oddx with ⟨n,rfl⟩,
       ring_nf,
       symmetry,
       rw int.modeq_iff_dvd,
       unfold has_dvd.dvd,
       use n^2,
       ring,
    },
  have h7 : (x^2 - 2*x + 4) = (x-1)^2 + 3:= by ring,
  rw ← h7 at h6,
  obtain ⟨p, hp, hpd, h8⟩  := do_we_have x h6,
  have h9 : ↑p∣y^2 + 1,
  { rw h2,
    exact dvd_mul_of_dvd_right hpd (x + 2), },
  haveI : fact (nat.prime p) := ⟨hp⟩,
  set yp : zmod p := y with hyp0,
  have hyp : yp^2 = -1,
  { rw ← zmod.int_coe_zmod_eq_zero_iff_dvd at h9,
    push_cast at h9,
    linear_combination h9, },
  apply zmod.mod_four_ne_three_of_sq_eq_neg_one hyp,
  rw nat.modeq at h8, 
  norm_num at h8,
  assumption,
end