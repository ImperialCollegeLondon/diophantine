import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic
import number_theory.legendre_symbol.quadratic_reciprocity
import number_theory.class_number.number_field


open_locale classical big_operators polynomial number_field
noncomputable theory

def quad_poly (n : ℤ) (R : Type*) [comm_ring R] [is_domain R] : R[X] := polynomial.X^2 - n 

@[derive [field, algebra ℚ, inhabited]]
def quad_field (n : ℤ): Type* := (quad_poly n ℚ).splitting_field

instance {n : ℤ} : polynomial.is_splitting_field ℚ (quad_field n) (quad_poly n ℚ) := 
begin
  apply polynomial.is_splitting_field.splitting_field,
end

instance quad_number_field (n : ℤ) :
  number_field (quad_field n) :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map ℚ (quad_field n)).injective,
  to_finite_dimensional := by {
    convert polynomial.is_splitting_field.finite_dimensional (quad_field n) (quad_poly n ℚ), } }
 
instance {p : ℤ}: is_fraction_ring (𝓞 (quad_field p )) (quad_field p ) := 
begin
 apply number_field.ring_of_integers.is_fraction_ring,
end

instance {n : ℤ} : finite_dimensional ℚ (quad_field n) := 
begin
  convert (quad_number_field n).to_finite_dimensional,
end

instance quad_class_group_finite {p : ℤ} :
  fintype (class_group (𝓞 (quad_field p )) (quad_field p )) :=
class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible 

def class_number_cond (n : ℤ) : Prop :=
(3 : ℕ).coprime $ fintype.card $
class_group (𝓞 $ quad_field n) $ quad_field n

def is_square_free (n : ℤ) : Prop := ¬ (∃ k, k^2 ∣ n)


--lemma key_lem (n : ℕ+) (x y : ℤ) (hn : is_square_free n) (hn4 : class_number_cond (-n)) 

lemma mordel_no_sol_fam (n : ℕ+) (x y : ℤ) (hn : is_square_free n) 
(hn2 : n ≡ 1 [ZMOD4] ∨ n ≡ 2 [ZMOD 4]) (hn3 : ¬ ( ∃ a, n = 3*a^2 +1 ∨ n = 3*a^2 -1)) 
(hn4 : class_number_cond (-n)) :  y^2 ≠ x^3 - n :=
begin

sorry,



end


