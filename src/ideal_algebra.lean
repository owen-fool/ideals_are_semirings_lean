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

/-- Next comes the operations -/

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


