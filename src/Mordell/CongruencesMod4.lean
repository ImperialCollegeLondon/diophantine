import tactic
import data.int.parity
import data.int.modeq
import data.nat.factorization.basic

lemma int.square_eq_zero_mod_four_of_even (x : ℤ)
  (hx : even x) : x^2 ≡ 0 [ZMOD 4] :=
begin
  have h: 0 < 2, by norm_num,
  rw int.modeq_zero_iff_dvd,
  rw even_iff_two_dvd at hx,
  have h4 : (4 : ℤ) = 2^2,
    {
      norm_num,
    },
  rw h4,
  rw int.pow_dvd_pow_iff,
  { exact hx,},
  {norm_num,},
end

lemma int.square_eq_one_mod_four_of_odd (x : ℤ)
  (hx : odd x) : x^2 ≡ 1 [ZMOD 4] :=
begin
   -- write x as 2*n+1
  rcases hx with ⟨n, rfl⟩,
  -- note that (2n+1)^2=4n^2+4n+1
  have h : (2 * n + 1)^2 = 4 * (n^2+n) + 1,
  -- this is true in any commutative ring so the `ring` tactic works
  { ring, },
  rw h,
  -- for convenience change a ≡ b to b ≡ a
  symmetry,
  -- The lemma `int.modeq_iff_dvd` says that
  -- a ≡ b mod n iff n divides b - a,
  rw int.modeq_iff_dvd,
  -- The definition of x ∣ y is ∃ c, y = x * c
  unfold has_dvd.dvd,
  -- so we have to prove there exists some c such that
  -- 4 * (n ^ 2 + n) + 1 - 1 = 4 * c
  -- and of course c=n^2+n works
  use (n^2+n),
  -- as the `ring` tactic will testify
  ring,
end

lemma int.square_ne_two_mod_four (x : ℤ) :
  ¬ (x^2 ≡ 2 [ZMOD 4]) :=
begin
  intro h,
  cases int.even_or_odd x with hx hx,
  { have h2:= x.square_eq_zero_mod_four_of_even hx,
    have h3: 0 ≡ 2 [ZMOD 4],
      {
        transitivity x^2,
        symmetry,
        exact h2,
        assumption,
      },
   unfold int.modeq at h3,
   norm_num at h3,},
  { have h2:= x.square_eq_one_mod_four_of_odd hx,
    have h3: 1 ≡ 2 [ZMOD 4],
      {
        transitivity x^2,
        symmetry,
        assumption,
        assumption,
      },
    unfold int.modeq at h3,
    norm_num at h3,
  }
end

lemma int.square_ne_three_mod_four (x : ℤ) :
  ¬ (x^2 ≡ 3 [ZMOD 4]) :=
begin
  intro h,
  cases int.even_or_odd x with hx hx,
  { have h2:= x.square_eq_zero_mod_four_of_even hx,
    have h3: 0 ≡ 3 [ZMOD 4],
      {
        transitivity x^2,
        symmetry,
        exact h2,
        assumption,
      },
   unfold int.modeq at h3,
   norm_num at h3,},
  { have h2:= x.square_eq_one_mod_four_of_odd hx,
    have h3: 1 ≡ 3 [ZMOD 4],
      {
        transitivity x^2,
        symmetry,
        assumption,
        assumption,
      },
    unfold int.modeq at h3,
    norm_num at h3,
  }
end

lemma modulo_eq (a b n : ℕ) (h: b < n) : a ≡ b [MOD n] ↔ ∃ m, a = n * m + b:=
begin
rw nat.modeq,
split,
intro h2,
{ have h1: b % n = b,
    { rw nat.mod_eq_of_lt,
     exact h,
    },
  rw h1 at h2,
  simp only [←nat.div_add_mod a n] {single_pass := tt},
  rw h2,
  use a/n,
},
{ intro h1,
  cases h1 with m hm,
  rw hm,
  have h3: n*m + b = b + n*m, by ring,
  rw h3,
  rw nat.add_mul_mod_self_left,
}
end

lemma odd_x_eq_one_or_three_mod_4 (x : ℕ) (hx: odd x) : x ≡ 1 [MOD 4] ∨ x ≡ 3 [MOD 4]:=
begin
rcases hx with ⟨n, rfl⟩,
rw modulo_eq,
rw modulo_eq,
{
cases nat.even_or_odd n with hn hn,
{left,
use n/2,
rcases hn with ⟨m, rfl⟩,
ring_nf,
norm_num,
},
{right,
use (n-1)/2,
rcases hn with ⟨m, rfl⟩,
norm_num,
ring,
},
},
{norm_num,},
{norm_num,},
end

lemma two_neq_3_mod_4 : ¬ ∃ (x : ℕ), 2^x ≡ 3 [MOD 4] :=
begin
intro h,
cases h with a h2,
rw modulo_eq at h2,
swap,
norm_num,
cases h2 with b h4,
have h5: 4 * b + 3 = 2*(2 * b + 1) + 1,
ring,
rw h5 at h4,
cases a,
ring_nf at h4,
rw h5 at h4,
linarith,
rw nat.succ_eq_add_one at h4,
rw nat.add_comm at h4,
have h6: a = 1 - 1 + a:= by ring,
rw h6 at h4,
rw pow_add at h4,
norm_num at h4,
have h7: even (2*2^a),
rw nat.even_iff,
exact nat.mul_mod_right 2 (2^a),
have h8: odd (2 * (2 * b + 1) + 1),
rw nat.odd_iff,
rw nat.add_mod,
norm_num,
rw h4 at h7,
exact nat.even_iff_not_odd.mp h7 h8,
end

lemma nat.prime.odd {p : ℕ} (hp : p.prime) (h : p ≠ 2) : odd p :=
hp.eq_two_or_odd'.resolve_left h

lemma one_mod_4_exp (x b: ℕ) : x ≡ 1 [MOD 4] → x^b ≡ 1 [MOD 4] :=
begin
intro h,
induction b with k hk,
norm_num,
rw nat.succ_eq_add_one,
rw pow_add,
norm_num,
rw nat.modeq at h hk ⊢,
norm_num at h hk ⊢,
rw nat.mul_mod,
rw h,
rw hk,
norm_num,
end



lemma three_modulo_four_prime_factor (x : ℕ) (hx: x ≡ 3 [MOD 4]) : ∃ (p : ℕ), p.prime ∧ p ∣ x ∧ p ≡ 3 [MOD 4] :=
begin
  induction x using nat.rec_on_pos_prime_pos_coprime with a b hab hb a b ha hb hcb iha ihb,
  swap,
  { norm_num at hx, },
  { refine ⟨a, hab, dvd_pow_self a hb.ne', _⟩,
    {
      { have h2: 2 ≠ a,
        { rintro rfl, apply two_neq_3_mod_4, use b, assumption, },
        have h1 := nat.prime.odd hab h2.symm,
        cases (odd_x_eq_one_or_three_mod_4 a h1) with h3 h4,
        swap,
        assumption,
        have h5 : a^b ≡ 1 [MOD 4] := one_mod_4_exp a b h3,
        exfalso,
        rw nat.modeq at h5 hx,
        rw h5 at hx,
        norm_num at hx,
      },
    },
  },
  { exfalso,
    rw nat.modeq at hx,
    norm_num at hx,},
  { suffices : a ≡ 3 [MOD 4] ∨ b ≡ 3 [MOD 4],
    { cases this with h1 h2,    
      { have ha1 : (∃ (p : ℕ), nat.prime p ∧ p ∣ a ∧ p ≡ 3 [MOD 4]):= by exact iha(h1),
        obtain ⟨p, hp, hpa, hpm⟩ := ha1,       
        have hab := dvd_mul_of_dvd_left hpa b,  
        refine ⟨p, hp, hab, hpm⟩,
      },
      { have hb1 : (∃ (p : ℕ), nat.prime p ∧ p ∣ b ∧ p ≡ 3 [MOD 4]):= by exact ihb(h2),
        obtain ⟨p, hp, hpb, hpm⟩ := hb1,       
        have hab := dvd_mul_of_dvd_right hpb a,  
        refine ⟨p, hp, hab, hpm⟩,
      },
    },   
    { norm_num [nat.modeq] at ⊢ hx,
      replace hx := hx.symm.trans (nat.mul_mod a b 4),
      have ha : a % 4 < 4 := nat.mod_lt a dec_trivial,
      have hb : b % 4 < 4 := nat.mod_lt b dec_trivial,
      revert ha hb hx,
      generalize : a % 4 = a',
      generalize : b % 4 = b',
      intros ha hb,
      revert a' ha b' hb,
      exact dec_trivial,    
    },
  },
end