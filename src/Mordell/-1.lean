import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity
import number_theory.zsqrtd.gaussian_int
import ring_theory.principal_ideal_domain

import Mordell.CongruencesMod4

local notation `ℤ[i]` := gaussian_int
local notation `i` := zsqrtd.sqrtd

--hard(ish)

instance : unique_factorization_monoid ℤ[i] := infer_instance


lemma y_pm_i_coprime (y : ℤ[i]) : is_coprime (y + i) (y - i):=
begin
unfold is_coprime,
sorry
end


example (x y : ℤ) (h : y^2 = x^3 -1) : x = 1 ∧ y =0 :=
begin
 have : (x^3 : ℤ[i]) = (y + (i : ℤ[i])) * (y - (i: ℤ[i])), by {ring_nf, 
 nth_rewrite 1 pow_two, 
 simp, 
 norm_cast, 
 simp [h] },
 have oddx: odd x,
  { by_contradiction evenx,
    rw ← int.even_iff_not_odd at evenx,
    rw even_iff_two_dvd at evenx,
    have hy2 : y^2 ≡ 7 [ZMOD 8],
    { rw h,
      rcases evenx with ⟨k, rfl⟩,
      apply int.modeq_of_dvd,
      exact dvd.intro (1-k^3) (by ring),
    },
    have h4:= int.square_ne_three_mod_four y,
    apply h4,
    have h6: (4 : ℤ ) ∣ 8:= by norm_num,
    have h5:= int.modeq.modeq_of_dvd h6 hy2,
    unfold int.modeq at h5 ⊢,
    rw h5,
    norm_num,
  },
have eveny: even y,
{ unfold odd at oddx,
  obtain ⟨k, rfl⟩ := oddx,
  norm_num at h,
  have htemp : even (y^2),
  { unfold even,
    use (4*k^3 + 6*k^2 + 3*k),
    rw h,
    ring,},
  have h2temp : 2 ≠ 0 := by norm_num,
  exact (int.even_pow' h2temp).mp htemp,},
  
sorry,
end



lemma test (a p : ℤ) (ha : 2^3 ∣ (2^2 * a^2)) : 2 ∣ a :=
begin
have h1 : (2 : ℤ)^2 ∣ 2^2 , by {exact dvd_rfl,},
have h2 : (2 : ℤ)^0 ∣ a^2 , by {norm_num},
have h3 : (2 : ℤ)^(2+0+1) ∣ (2^2 * a^2), by {apply ha,},
have := succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (int.prime_two) h1 h2 h3,
cases this,
exfalso,
rw pow_add at this,
simp at this,
norm_num at this,
simp at this,
apply prime.dvd_of_dvd_pow int.prime_two this,

end
