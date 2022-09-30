import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4


lemma neg_one_square (p : ℤ) (hp : prime p) (h : ∃ (n : ℤ), n^2 ≡ -1 [ZMOD p]) : p ≡ 3 [ZMOD 4] :=
begin
--this is maybe somewhere in mathlib
sorry,
end


lemma neg_two_square_mod_p (p : ℤ) (hp : prime p) (h : ∃ (n : ℤ), n^2 ≡ -2 [ZMOD p]) : 
  (p ≡ 1 [ZMOD 8] ∨ p ≡ 3  [ZMOD 8]) :=
begin
--this is maybe somewhere in mathlib
sorry,
end

example (x y : ℤ) : y^2 ≠ x^3 - 24 :=
begin
sorry,


end