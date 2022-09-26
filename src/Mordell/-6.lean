import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4

--Easy(ish)

lemma prime_factor_congr_3_mod_8 (x : ℤ) (h : x^2 + 2*x + 4 ≡ 3 [ZMOD 8]) :
  ∃ (p : ℕ), p.prime ∧ (p : int) ∣ (x^2 + 2*x + 4)  ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5  [MOD 8]) := 
begin



sorry,
end

example (x y : ℤ) : y^2 ≠ x^3 - 6 :=
begin
  intro heq,
  have oddx: odd x, by {sorry},
  have oddy: odd y, by {sorry},
  have h2 : y^2 -2 = (x-2)*(x^2 + 2*x + 4), by {sorry},

sorry, 
end