import ideal_definitions
import ring_finite_sums

local infixr ` + ` : 80 := plus
local infixr ` * ` : 80 := mult

/-- Definitions and lemmas we will need for proving that the Ideals of a Ring form a Semi-Ring -/

def Ideal_one {R : Ring} : Ideal R :=
{ I := λ x, true, -- every element of the ring is in this ideal
  ideal_axioms :=
  begin
   unfold set.mem,
   simp,
   cc,
  end
}

def Ideal_zero {R : Ring} : Ideal R :=
{ I := {x | x = zero}, -- this ideal has only one element, zero
  ideal_axioms :=
  begin
   unfold set.mem,
   split,
   { split,
     { exact rfl, },
     { split,
       { intros x y hx hy,
         calc
          x + y = zero : by { cases hx, cases hy, exact zero_plus_neutral zero },
        },
        { intros x x' hxx' hx,
          apply plus_inv_unique zero,
          cases hx,
          split,
          { exact hxx', },
          { exact zero_plus_neutral zero, }, }, }, },
     { split,
       { intros x y hx,
         cases hx, 
         exact zero_annihilates_left y, },
       { intros x y hx,
         cases hx,
         exact zero_annihilates_right y, }, },
  end /- should i have done more calcs in here? -/ }

/- Apparently i found this saved some work in full_proof, using the ∈ symbol in the type
   specification meant that the system couldn't follow what the implicit Ring was  -/
lemma Ideal_zero_mems_are_zero {R : Ring} : ∀ x : R.R, Ideal_zero.I x → x = zero :=
begin
 intros x hx,
 exact hx,
end

/- Here is where we begin to make use of the finite sum file -/

-- the set of finite sums of multiples of elements of a nonempty subset of a Ring forms an Ideal
def fin_sum_set {R : Ring} (X : set R.R) (H : ∃ x : R.R, x ∈ X) : Ideal R :=
{ I := {p | ∃ n : ℕ, ∃ f : ℕ → R.R, 
            p = fin_sum f n ∧ ∀ n : ℕ, ∃ x ∈ X, ∃ y z : R.R, f n = y * x * z},
  ideal_axioms :=
  begin
   unfold set.mem,
   split,
   { split,
     { existsi 0,
       existsi λ n, zero,
       split,
       { exact rfl, },
       { intro n,
         cases H with x hx,
         existsi x,
         existsi hx, 
         existsi zero,
         existsi zero,
         symmetry,
         calc
          zero * x * zero = zero : by { rw zero_annihilates_right, rw zero_annihilates_left },
       }, },
     { split,
       { intros x y hx hy,
         cases hx with nx hx,
         cases hx with fx hx,
         cases hx with eqx hx,
         cases hy with ny hy,
         cases hy with fy hy,
         cases hy with eqy hy,
         existsi nat.succ (nat.add nx ny),
         existsi add_fun nx fx fy,
         split,
         { calc
            x + y = (fin_sum fx nx) + fin_sum fy ny : by { rw eqx, rw eqy }
              ... = (fin_sum_sum nx fx fy) (nat.succ (nat.add nx ny)) 
                                                    : by rw ← add_fin_sum.sum_is_sum
              ... = fin_sum (add_fun nx fx fy) (nat.succ (nat.add nx ny)) 
                                                    : by { symmetry, 
                                                           exact add_fin_sum.add_fin_sum nx fx fy
                                                                  (nat.succ (nat.add nx ny)) }, 
         },
         {intro n,
          induction n with n indh,
          { specialize hx 0,
            exact hx, },
          { have dec := lt_decidable nx n,
            have h : add_fun nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n))
                                                         (fy (nat.succ n - nat.succ nx)),
            { exact rfl, },
            cases dec,
            { specialize hx (nat.succ n),
              cases hx with x' hx,
              cases hx with hx' hx,
              cases hx with xl hx,
              cases hx with xr hx,
              existsi x',
              existsi hx',
              existsi xl,
              existsi xr,
              calc
               add_fun nx fx fy (nat.succ n) = fx (nat.succ n) : by simp [h, dec]
                                         ... = xl * x' * xr    : by exact hx, },
            { specialize hy (nat.succ n - nat.succ nx),
              have h' : add_fun nx fx fy (nat.succ n) = fy (nat.succ n - nat.succ nx),
              { simp [h, dec] },
              rw h',
              exact hy, -- these last two blocks essentially shows two different methods for
                        -- arriving at the same result: that the terms of the sum of finite sums
                        -- of multiples of elements of X are multiples of elements of X
                        -- themselves, one might be clearer, the other is definitely shorter
            }, }, }, },
       { intros x x' hxx' hx,
         cases hx with nx hx,
         cases hx with fx hx,
         cases hx with eqx hx,
         have n_one : ∃ neg_one : R.R, one + neg_one = zero,
         { exact plus_inv one, },
         cases n_one with neg_one n_one,
         existsi nx,
         existsi mul_fun neg_one fx,
         split,
         { apply plus_inv_unique x,
           split,
           { exact hxx' },
           { calc
              x + fin_sum (mul_fun neg_one fx) nx 
                  = x + neg_one * (fin_sum fx nx) : by rw ← mul_fin_sum.mul_fin_sum neg_one fx nx
              ... = x + neg_one * x               : by rw ← eqx
              ... = zero                          : by exact negative_one neg_one x n_one, }, },
         { intro n,
           specialize hx n,
           cases hx with x' hx,
           cases hx with hx' hx,
           cases hx with xl hx,
           cases hx with xr hx,
           existsi x',
           existsi hx',
           existsi neg_one * xl,
           existsi xr,
           calc
            mul_fun neg_one fx n = neg_one * fx n : by exact rfl
                             ... = neg_one * xl * x' * xr : by rw hx
                             ... = (neg_one * xl) * x' * xr 
                                                  : by exact mult_assoc neg_one xl (x' * xr) },
   }, }, },
   { split,
     { intros x y hx,
       cases hx with nx hx,
       cases hx with fx hx,
       cases hx with eqx hx,
       existsi nx,
       existsi mul_fun' y fx,
       split,
       { calc
          x * y = (fin_sum fx nx) * y : by rw eqx
            ... = fin_sum (mul_fun' y fx) nx : by exact mul_fin_sum.mul_fin_sum' y fx nx, },
       { intro n,
         specialize hx n,
         cases hx with x' hx,
         cases hx with hx' hx,
         cases hx with xl hx,
         cases hx with xr hx,
         existsi x',
         existsi hx',
         existsi xl,
         existsi xr * y,
         calc
          mul_fun' y fx n = (fx n) * y : by exact rfl
                      ... = (xl * x' * xr) * y : by rw hx
                      ... = xl * (x' * xr) * y : by { symmetry, exact mult_assoc xl (x' * xr) y }
                      ... = xl * x' * xr * y   : by rw ← mult_assoc x' xr y, }, },
     { intros x y hx,
       cases hx with nx hx,
       cases hx with fx hx,
       cases hx with eqx hx,
       existsi nx,
       existsi mul_fun y fx,
       split,
       { calc
          y * x = y * fin_sum fx nx : by rw eqx
            ... = fin_sum (mul_fun y fx) nx : by exact mul_fin_sum.mul_fin_sum y fx nx, },
       { intro n,
         specialize hx n,
         cases hx with x' hx,
         cases hx with hx' hx,
         cases hx with xl hx,
         cases hx with xr hx,
         existsi x',
         existsi hx',
         existsi y * xl,
         existsi xr,
         calc
          mul_fun y fx n = y * fx n : by exact rfl
                     ... = y * (xl * x' * xr) : by rw hx
                     ... = (y * xl) * x' * xr : by exact mult_assoc y xl (x' * xr), }, }, },
  end
}

/-- Next come the operations -/

def Ideal_plus {R : Ring} (I I' : Ideal R) : Ideal R :=
{ I := {z | ∃ (x y : R.R), x ∈ I.I ∧ y ∈ I'.I ∧ z = x + y},
  ideal_axioms :=
  begin
   split,
   { split,
     { existsi zero,
       existsi zero,
       split,
       { exact zero_mem_Ideal I, },
       { split,
         { exact zero_mem_Ideal I', },
         { calc
            zero = zero + zero : by { symmetry, exact zero_plus_neutral zero, }, }, }, },
     split,
     { intros x y hx hy,
       -- the last time i tried to import tactics i ran out of memory, and i'm not sure how to 
       -- more specifically just import rcases
       cases hx with x' hx,
       cases hx with x'' hx,
       cases hx with hx' hx,
       cases hx with hx'' hx,
       cases hy with y' hy,
       cases hy with y'' hy,
       cases hy with hy' hy,
       cases hy with hy'' hy,
       existsi (x' + y'),
       existsi (x'' + y''),
       split,
       { exact (subgroup_under_addition I).2.1 x' y' hx' hy' },
       { split,
         { exact (subgroup_under_addition I').2.1 x'' y'' hx'' hy'' },
         { calc
            x + y    = (x' + x'') + (y' + y'') : by { rw hx, rw hy }
                 ... = x' + x'' + y' + y''     : by rw ← plus_assoc
                 ... = x' + (y' + y'') + x''   : by rw plus_comm x'' (y' + y'')
                 ... = x' + y' + y'' + x''     : by rw ← plus_assoc
                 ... = (x' + y') + x'' + y''   : by { rw plus_assoc, rw plus_comm y'' x'' },
         }, }, },
     intros x x' hxx' hx,
     cases hx with y' hx,
     cases hx with y'' hx,
     cases hx with hy' hx,
     cases hx with hy'' hx,
     have H : ∃ a' : R.R, y' + a' = zero,
     { exact plus_inv y', },
     cases H with a' ha',
     have H : ∃ a'' : R.R, y'' + a'' = zero,
     { exact plus_inv y'', },
     cases H with a'' ha'',
     have h : x + a' + a'' = zero,
     { calc
        x + a' + a''     = y' + y'' + a' + a''   : by { rw hx, rw ← plus_assoc }
                     ... = y' + (y'' + a'') + a' : by { rw plus_comm a' a'', 
                                                        rw plus_assoc y'' a'' a' }
                     ... = y' + zero + a'        : by rw ha''
                     ... = y' + a' + zero        : by rw plus_comm zero a'
                     ... = (y' + a') + zero      : by exact plus_assoc y' a' zero
                     ... = zero + zero           : by rw ha'
                     ... = zero                  : by exact zero_plus_neutral zero, },
     existsi a',
     existsi a'',
     split,
     { exact (subgroup_under_addition I).2.2 y' a' ha' hy', },
     split,
     { exact (subgroup_under_addition I').2.2 y'' a'' ha'' hy'', },
     apply plus_inv_unique x,
     exact ⟨hxx', h⟩, },
   { split,
     { intros x y hx,
       cases hx with x' hx,
       cases hx with x'' hx,
       cases hx with hx' hx,
       cases hx with hx'' hx,
       existsi x' * y,
       existsi x'' * y,
       split,
       { exact (multiplication_conditions I).1 x' y hx', },
       { split,
         { exact (multiplication_conditions I').1 x'' y hx'', },
         { calc
            x * y     = (x' + x'') * y : by rw hx
                  ... = (x' * y) + x'' * y : by exact distributivity_laws.2 x' x'' y }, }, },
     { intros x y hx,
       cases hx with x' hx,
       cases hx with x'' hx,
       cases hx with hx' hx,
       cases hx with hx'' hx,
       existsi (y * x'),
       existsi (y * x''),
       split,
       { exact (multiplication_conditions I).2 x' y hx', },
       { split,
         { exact (multiplication_conditions I').2 x'' y hx'', },
         { calc
            y * x     = y * (x' + x'') : by rw hx
                  ... = (y * x') + y * x'' : by exact distributivity_laws.1 y x' x'', }, }, }, },
  end }
local infixr ` ⨁ ` : 80 := Ideal_plus


