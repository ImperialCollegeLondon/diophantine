import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity


import Mordell.CongruencesMod4

lemma consecutive_cubes (n : ℤ) (hn : ∃ m, n = m^3) (hn1 : ∃ k, n+1 = k^3) : n = -1 ∨ n = 0 :=
begin
sorry,
end


example (x y : ℤ) (h : y^2 = x^3 + 16) : x = 0 ∧ (y.nat_abs = 4) :=
begin
 have : x^3 = (y - 4) * (y + 4), by {sorry},
 have  eveny : even y, by {sorry},
 have evenx : even x, by {sorry},
 have h4y : 4 ∣ y, by {sorry},
 have h4x : 4 ∣ y, by {sorry},
 sorry,
end