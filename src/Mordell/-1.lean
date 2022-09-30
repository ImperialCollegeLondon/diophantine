import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity
import number_theory.zsqrtd.gaussian_int
import ring_theory.principal_ideal_domain

local notation `ℤ[i]` := gaussian_int


--hard(ish)

instance : unique_factorization_monoid ℤ[i] := infer_instance


example (x y : ℤ) (h : y^2 = x^3 -1) : x = 1 ∧ y =0 :=
begin
 have : (x^3 : ℤ[i]) = (y + (zsqrtd.sqrtd : ℤ[i])) * (y - (zsqrtd.sqrtd: ℤ[i])), by {ring_nf, 
 nth_rewrite 1 pow_two, 
 simp, 
 norm_cast, 
 simp [h] },
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
