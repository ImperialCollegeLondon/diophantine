import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity
import number_theory.zsqrtd.gaussian_int
import ring_theory.principal_ideal_domain

local notation `ℤ[i]` := gaussian_int

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