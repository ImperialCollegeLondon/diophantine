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