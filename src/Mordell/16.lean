import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4

--medium(ish)

def is_cube (n : ℤ) : Prop := ∃ (m : ℤ), n = m^3 


lemma diff_of_cubes (n m : ℤ) (hn : is_cube n) (hm : is_cube m) (hn2 : odd n) (hm2 : odd m) :
  n - m ≠ 8 :=
begin
  sorry,
end


lemma consecutive_cubes (n : ℤ) (hn : is_cube n) (hn1 : is_cube (n+1)) : n = -1 ∨ n = 0 :=
begin
left,
sorry,
end


example (x y : ℤ) (h : y^2 = x^3 + 16) : x = 0 ∧ (y.nat_abs = 4) :=
begin
 have h₀ : x^3 = (y - 4) * (y + 4), 
 {  have h₁ : x^3 = y^2 - 16,
    { rw h,
      ring},
    rw h₁,
    ring},
 have eveny : even y,
 {  sorry},
 have evenx : even x,
 {  cases eveny,
    rw eveny_h at h,
    have h₁ : (2*  eveny_w) ^ 2 = x ^ 3 + 16,
    {  rw ← h,
      ring},
    have h₂ : 4 * eveny_w ^ 2 = x^3 + 16,
    { rw ← h₁,
      ring},
    have h₃ : 4 * eveny_w^2 - 16 = x^3,
    { rw h₂,
      ring},
    have h₄ : (2* eveny_w^2 - 8) + (2* eveny_w^2 - 8) = x^3,
      { rw ← h₃,
        ring},
    clear h₁ h₂ h₃,
    have h₅ : even (x^3),
    { unfold even,
      use 2* eveny_w^2 - 8,
      rw h₄},
    rw int.even_pow' at h₅,
    swap,
    norm_num,
    assumption},
 have h4y : 4 ∣ y,
 {  have h₁: 8 ∣ (x^3 + 16),
    { cases evenx,
      rw evenx_h,
      ring_nf,
      have h₂ : 8 * evenx_w^3 + 16 = 8 * (evenx_w^3 +2) := by ring,
      rw h₂,
      exact dvd.intro (evenx_w ^ 3 + 2) rfl},
  have h₂ : 8 ∣ y^2 := by rwa h,
  rw even_iff_exists_two_nsmul at eveny,
  simp at eveny,
  obtain⟨a, ha⟩:= eveny,
  rw ha at ⊢ h₂,
  have h₅ := int.mul_div_cancel' h₂,
  have h₆: (2 : ℤ)^2 * a^2 = (2*a)^2 := by ring,
  rw ← h₆ at h₅,
  have h₇ : 2^2 * (2 ^ 2 * a ^2 / 2 ^ 3) = 2 * a ^ 2,
  { norm_num at h₅ ⊢,
    have htemp : (8 : ℤ) = 2 * 4 := by norm_num,
    have htemp2 : (4 : ℤ) = 2 * 2 := by norm_num,
    rw htemp at h₅,
    rw htemp2 at h₅,
    simp_rw mul_assoc at h₅,
    have h₈ : (2 : ℤ) ≠ 0 := by exact two_ne_zero,
    have := mul_left_cancel₀ h₈ h₅,
    rw ← this,
    ring_nf},
  have h₉ : 2 * (2 ^ 2 * a ^2 / 2 ^ 3) = a ^ 2,
  { norm_num at h₇ ⊢,
    have htemp : (8 : ℤ) = 2 * 4 := by norm_num,
    have htemp2 : (4 : ℤ) = 2 * 2 := by norm_num,
    rw htemp at h₇,
    rw htemp2 at h₇,
    simp_rw mul_assoc at h₇,
    have h₈ : (2 : ℤ) ≠ 0 := by exact two_ne_zero,
    have := mul_left_cancel₀ h₈ h₇,
    rw ← this,
    simp,
    ring_nf,
    apply int.mul_div_cancel_left,
    norm_num},
    norm_num at h₉,
    have := dvd.intro (4 * a ^ 2 / 8) h₉,
    have := prime.dvd_of_dvd_pow int.prime_two this,
    have : (4 : ℤ) = 2 * 2 := by norm_num,
    rw this,
    apply mul_dvd_mul_left,
    assumption,},
 have h4x : 4 ∣ x,
 {  have h₁ := int.mul_div_cancel' h4y,
    rw ← h₁ at h,
    rw mul_pow at h,
    norm_num at h,
    have h₂ : 16 * ((y/4)^2 - 1) = x^3,
    { have htemp : 16 * (y/4)^2 - 16 = x^3,
      { rw h,
        ring},
      rw ← htemp,
      ring},
    have h16x3 := dvd.intro ((y/4)^2 - 1) h₂,
    have h₃ := int.mul_div_cancel' h16x3,
    obtain⟨a, ha⟩:= evenx,
    rw ha at h₃,
    
    sorry},
 sorry,
end