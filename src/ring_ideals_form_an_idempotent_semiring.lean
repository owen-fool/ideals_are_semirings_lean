import ideal_algebra

local infixr ` + ` : 80 := plus
local infixr ` * ` : 80 := mult
local infixr ` ⨁ ` : 80 := Ideal_plus
local infixr ` ⨂ ` : 80 := Ideal_mult

/-- See, e.g. here: https://en.wikipedia.org/wiki/Semiring -/
structure is_idempotent_semiring (X : Type _) :=
(plus : X → X → X)
(mult : X → X → X)
(zero' : X)
(one'  : X)
(plus_assoc : ∀ x y z : X, plus x (plus y z) = plus (plus x y) z)
(plus_comm  : ∀ x y   : X, plus x y = plus y x)
(plus_iden  : ∀ x     : X, plus x zero' = x)
(mult_assoc : ∀ x y z : X, mult x (mult y z) = mult (mult x y) z)
(mult_liden : ∀ x     : X, mult one' x = x)
(mult_riden : ∀ x     : X, mult x one' = x)
(lm_distrib : ∀ x y z : X, mult x (plus y z) = plus (mult x y) (mult x z))
(rm_distrib : ∀ x y z : X, mult (plus x y) z = plus (mult x z) (mult y z))
(zero_lanni : ∀ x     : X, mult zero' x = zero')
(zero_ranni : ∀ x     : X, mult x zero' = zero')
(plus_idemp : ∀ x     : X, plus x x = x)

theorem ring_ideals_form_an_idempotent_semiring {R : Ring} :
is_idempotent_semiring (Ideal R) :=
{ plus  := Ideal_plus,
  mult  := Ideal_mult,
  zero' := Ideal_zero,
  one'  := Ideal_one,
  plus_assoc :=
  begin -- addition of Ideals is associative!
   intros w x y,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,  -- we now see that the two ideals are equal if, for an arbitrary element of the ring,
           -- it is an element of one of the ideals iff it is an element of the other, we 
           -- split, to consider the two directions of the biconditional is turn
   { intro hz,
     cases hz with x' hz, 
     cases hz with y' hz,
     cases hz with hx' hz,
     cases hz with hy' hz,
     cases hy' with x'' hy',
     cases hy' with y'' hy',
     cases hy' with hx'' hy',
     cases hy' with hy'' hy',
     rw hy' at hz,
     -- we are required to show that z is an element of (w ⨁ x) ⨁ y, we know that:
     -- z = x' + x'' + y', that x' is an element of w, that x'' is an element of x and that y' is
     -- an element of y, by associativity z = (x' + x'') + y', and then there isn't much more work
     -- to do.
     existsi x' + x'',
     existsi y'',
     split,
     { existsi x',
       existsi x'',
       split,
       { exact hx', },
       { split,
         { exact hx'', },
         { exact rfl, }, }, }, -- and we have succesfully shown that x' + x'' ∈ w ⨁ x
     { split,
       { exact hy'' }, -- and y' ∈ y
       { calc
          z     = x' + x'' + y'' : by exact hz
            ... = (x' + x'') + y'' : by exact plus_assoc x' x'' y'', }, }, },
          -- so, z = (x' + x'') + y'' ∈ (w ⨁ x) ⨁ y as required
   { intro hz, 
     cases hz with x' hz, -- the second part of this proof proceeds in substantially the same way,
     cases hz with y' hz, -- only the associativity runs in the other direction
     cases hz with hx' hz,-- in a sense, the type of Ideals inherits its associativity from the
     cases hz with hy' hz,-- associativity of the corresponding ring
     cases hx' with x'' hx',
     cases hx' with y'' hx',
     cases hx' with hx'' hx',
     cases hx' with hy'' hx',
     rw hx' at hz,
     existsi x'',
     existsi y'' + y',
     split,
     { exact hx'', },
     { split,
       { existsi y'',
         existsi y',
         split,
         { exact hy'' },
         { split,
           { exact hy', },
           { exact rfl, }, }, },
       { calc
          z     = (x'' + y'') + y' : by exact hz
            ... = x'' + y'' + y'   : by { symmetry, exact plus_assoc x'' y'' y' } }, }, },
  end,
  plus_comm  :=
  begin -- addition of Ideals is commutative!
   intros x y,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split, -- these few lines will appear in most sections of the proof of this theorem,
          -- we demonstrate that the biconditional about membership of our Ideals is sufficient 
          -- for equality of those Ideals, and then we split and prove each direction in turn
   { intro hz,
     cases hz with x' hz,
     cases hz with y' hz,
     cases hz with hx' hz,
     cases hz with hy' hz,
     existsi y',
     existsi x',
     split,          -- we must show that z ∈ y ⨁ x, we know that z = x' + y', x' ∈ x, y' ∈ y
     { exact hy', }, -- so we can use commutativity of addition in the ring   
     { split,
       { exact hx', },
       { calc
          z     = x' + y' : by exact hz
            ... = y' + x' : by exact plus_comm x' y', }, }, },
   { intro hz,
     cases hz with x' hz,
     cases hz with y' hz,
     cases hz with hx' hz,
     cases hz with hy' hz,
     existsi y',
     existsi x',
     split,
     { exact hy', },
     { split,
       { exact hx', },
       { calc
          z     = x' + y' : by exact hz
            ... = y' + x' : by exact plus_comm x' y',  }, }, },
  end,
  plus_iden  :=
  begin -- zero Ideal is additive identity!
   intro x,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split, -- see, here it is again, same as in the last two sections
   { intro hz,
     cases hz with x' hz,
     cases hz with y' hz,
     cases hz with hx' hz,
     cases hz with hy' hz,
     -- now, we want to show that z ∈ x, we know that z = x' + y', that y' ∈ Ideal_zero and that
     -- x' ∈ x, we now show that y' can only be zero, so x' must be equal to z, so z ∈ x.
     have h : y' = zero,
     { exact Ideal_zero_mems_are_zero y' hy', },
     rw h at hz,
     have h' : z = x',
     { calc
        z     = x' + zero : by exact hz
          ... = x'        : by exact zero_plus_neutral x',  },
     rw h',
     exact hx', },
   { intro hz,
     -- we must show that z ∈ x ⨁ Ideal_zero, we know that z ∈ x, and showing that 
     -- zero ∈ Ideal_zero would be trivial, and z + zero = z, therefore z ∈ x ⨁ Ideal_zero
     existsi z,
     existsi zero,
     split,
     { exact hz, },
     { split,
       { exact zero_mem_Ideal Ideal_zero },
       { calc
          z     = z + zero : by { symmetry, exact zero_plus_neutral z, }, }, }, },
  end,
  mult_assoc :=
  begin -- multiplication of Ideals is associative!
   -- all of the material on finite sums really comes into play here
   intros w y z,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hx,
     -- we know that x ∈ w ⨂ y ⨂ z and we want to show that it is in (w ⨂ y) ⨂ z, from the
     -- material on finite sums in the ideal_algebra file, we know that elements of the product
     -- ideal are finite sums of multiples of products of elements of the component ideals of the
     -- product, and then we can use what we know about the conditions for finite sums being
     -- elements of ideals to proceed.
     specialize hx (fin_sum_ideal (set_ideal_mult w (y ⨂ z)) (nonempty_set_ideal_mult w (y ⨂ z)))
                   (set_ideal_mult_in_mult_set w (y ⨂ z)),
     cases hx with nx hx,
     cases hx with fx hx,
     cases hx with eqx hx,
     rw eqx, -- eqx is the premise telling us that x is a finite sum of elements of the ring
     apply fin_sum_member_condition ((w ⨂ y) ⨂ z) fx nx,
     intro n, -- we consider an arbitrary value of the function fx, to show that the finite sum
     specialize hx n, -- membership condition holds for x.
     intros I hI,
     cases hx with x' hx,
     cases hx with hx' hx,
     cases hx' with y' hx',
     cases hx' with hy' hx',
     cases hx' with y'' hx',
     cases hx' with hy'' hx',
     specialize hy'' (fin_sum_ideal (set_ideal_mult y z) (nonempty_set_ideal_mult y z))
                     (set_ideal_mult_in_mult_set y z),
     cases hx with q hx,
     cases hx with p hx,
     rw hx, -- we know that each term of these finite sums is a multiple of products of terms in
     apply (multiplication_conditions I).2, -- w and terms in (y ⨂ z), by definition of ideals
     apply (multiplication_conditions I).1, -- we only need to show that those products are in
                                            -- the set we are interested in.
     cases hy'' with ny'' hy'', -- A term in y ⨂ z is a finite sum, so the product of such a term
     cases hy'' with fy'' hy'', -- and a term in w is a multiple of a finite sum, and we know that
     cases hy'' with eqy'' hy'',-- multiples of finite sums are finite sums, so after a little
     have h : x' = fin_sum (mul_fun y' fy'') ny'', -- rewriting we can apply our membership 
     { calc                                        -- condition again.
        x'     = y' * y'' : by exact hx'
           ... = y' * (fin_sum fy'' ny'') : by rw eqy''
           ... = fin_sum (mul_fun y' fy'') ny'' : by
                                                  exact mul_fin_sum.mul_fin_sum y' fy'' ny'' },
     rw h,
     apply fin_sum_member_condition I (mul_fun y' fy'') ny'',
     intro n',
     specialize hy'' n',
     cases hy'' with x'' hy'',
     cases hy'' with hx'' hy'',
     cases hy'' with y''' hy'',
     cases hy'' with z'' hy'',
     have h' : mul_fun y' fy'' n' = y' * (fy'' n'),
     { exact rfl, },
     have h'' : mul_fun y' fy'' n' = y' * y''' * x'' * z'',
     { calc
        mul_fun y' fy'' n'     = y' * fy'' n' : by exact h'
                           ... = y' * y''' * x'' * z'' : by rw hy'', },
     rw h'',
     cases hx'' with x''' hx'',
     cases hx'' with hx''' hx'',
     cases hx'' with z''' hx'',
     cases hx'' with hz''' hx'',
     have h''' : (y' * y''') * x''' ∈ (w ⨂ y).I,
     { intros I' hI',
       specialize hI' (y' * y''') x''',
       apply hI',
       { apply (multiplication_conditions w).1,
         exact hy', },
       { exact hx''', }, },
     have h'''' : y' * y''' * x'' * z''  -- we break up and rewrite our product so that its
                = ((y' * y''') * x''') * (z''' * z''), -- membership in the mult-set can be proved
     { calc                                            -- directly.
        y' * y''' * x'' * z''     = y' * y''' * (x''' * z''') * z'' : by rw hx''
                              ... = y' * y''' * x''' * z''' * z'' : by 
                                                                    rw ← mult_assoc x''' z''' z''
                              ... = (y' * y''') * x''' * z''' * z'' : by rw mult_assoc
                              ... = ((y' * y''') * x''') * z''' * z'' : by rw mult_assoc, },
     rw h'''',
     apply hI,
     { exact h''', },
     { apply (multiplication_conditions z).1,
       exact hz''', }, }, -- so ends the first part of the proof of multiplication's associativity
   {intro hx,
    specialize hx (fin_sum_ideal (set_ideal_mult (w ⨂ y) z) (nonempty_set_ideal_mult (w ⨂ y) z))
                  (set_ideal_mult_in_mult_set (w ⨂ y) z),
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    rw eqx,
    apply fin_sum_member_condition (w ⨂ y ⨂ z) fx nx,
    intro n,
    specialize hx n,
    intros I hI,
    cases hx with x' hx,
    cases hx with hx' hx,
    cases hx' with y' hx',
    cases hx' with hy' hx',
    cases hx' with y'' hx',
    cases hx' with hy'' hx',
    specialize hy' (fin_sum_ideal (set_ideal_mult w y) (nonempty_set_ideal_mult w y))
                    (set_ideal_mult_in_mult_set w y),
    cases hx with q hx,
    cases hx with p hx,
    rw hx,
    apply (multiplication_conditions I).2,
    apply (multiplication_conditions I).1,
    cases hy' with ny' hy',
    cases hy' with fy' hy',
    cases hy' with eqy' hy',
    have h : x' = fin_sum (mul_fun' y'' fy') ny',
    { calc
       x'     = y' * y'' : by exact hx'
          ... = (fin_sum fy' ny') * y'' : by rw eqy'
          ... = fin_sum (mul_fun' y'' fy') ny' : by
                                                 exact mul_fin_sum.mul_fin_sum' y'' fy' ny' },
    rw h,
    apply fin_sum_member_condition I (mul_fun' y'' fy') ny',
    intro n',
    specialize hy' n',
    cases hy' with x'' hy',
    cases hy' with hx'' hy',
    cases hy' with y''' hy',
    cases hy' with z'' hy',
    have h' : mul_fun' y'' fy' n' = (fy' n') * y'',
    { exact rfl, },
    have h'' : mul_fun' y'' fy' n' = y''' * x'' * z'' * y'',
    { calc
       mul_fun' y'' fy' n'     = (fy' n') * y'' : by exact h'
                           ... = (y''' * x'' * z'') * y'' : by rw hy'
                           ... = y''' * (x'' * z'') * y'' : by rw ← mult_assoc
                           ... = y''' * x'' * z'' * y''   : by rw ← mult_assoc x'' z'' y'', },
    rw h'',
    cases hx'' with x''' hx'',
    cases hx'' with hx''' hx'',
    cases hx'' with z''' hx'',
    cases hx'' with hz''' hx'',
    have h''' : z''' * z'' * y'' ∈ (y ⨂ z).I,
    { intros I' hI',
      specialize hI' z''' (z'' * y''),
      apply hI',
      { exact hz''', },
      { apply (multiplication_conditions z).2,
        exact hy'', }, },
    have h'''' : y''' * x'' * z'' * y'' 
               = (y''' * x''') * (z''' * z'' * y''),
    { calc
       y''' * x'' * z'' * y''     = y''' * (x''' * z''') * z'' * y'' : by rw hx''
                              ... = y''' * x''' * z''' * z'' * y'' : by 
                                                                     rw ← mult_assoc x''' z'''
                                                                                    (z'' * y'')
                              ... = (y''' * x''') * z''' * z'' * y'' : by rw mult_assoc, },
    rw h'''',
    apply hI,
    { apply (multiplication_conditions w).2,
      exact hx''', },
    { exact h''', }, },
  /- The proof of associativity is essentially the same is both directions, the basic idea is that
     an element is contained in an Ideal product if it is contained in every Ideal which contains
     all of the products of elements of the Ideals that make up the product, amongst those Ideals
     (the Ideals containing the products of elements) is the Ideal which contains only finite sums
     of multiples of products of elements of those Ideals, so each element of any ideal product is
     expressable as a finite sum. A finite sum is contained in an Ideal if each one of its terms
     is contained in that Ideal, and the terms of the finite sums expressing elements of our Ideal
     product are long multiples of elements of our ring. We are considering Ideal products where
     one of the terms is itself an Ideal product, so the terms of the finite sum contain,
     themselves, a finite sum, in fact, each term is re-expressible as a finite sum itself, but 
     this is no problem, since we can then use the same machinery to show that the term is in the
     Ideal product, by showing that each term of this new finite sum we have expressed it as is 
     so. We know that an element of the Ring is in our Ideal product if it's a product of elements
     of the Ring whose terms are in the terms of our Ideal product, so we use associativity of 
     multiplication in the Ring to rewrite our term of our finite sum as such a product, then we
     can complete the proof that the element is contained in the other Ideal product. -/
  end,
  mult_liden :=
  begin -- one Ideal is multiplicative identity from the left!
   intro w,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hx,
     specialize hx w, -- x ∈ w if w contains all products of a term in w and a term in Ideal_one
     apply hx,
     exact mult_set_self_right w Ideal_one, /- and w does -/ },
   { intros hx I hI,
     specialize hI one x, -- x ∈ Ideal_one ⨂ w if, for arbitrary I, I contains all products of
                          -- an element of Ideal_one and an element of w, implies I contains x,
                          -- the antecedant implies that I contains one * x, and we're done.
     rw ← one_mult_neutral_left x,
     apply hI,
     { have t : true,
       { cc, },
       exact t, }, -- silly trivial proof that one ∈ Ideal_one
     { exact hx, }, },
  end,
  mult_riden :=
  begin -- one Ideal is multiplicative identity from the right!
   intro w,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split, -- the body of this proof is almost identical to that above
   { intro hx,
     exact hx w (mult_set_self_left w Ideal_one), },
   { intros hx I hI,
     rw ← one_mult_neutral_right x,
     apply hI,
     { exact hx, },
     { have t : true,
       { cc, },
       exact t, }, },
  end,
  lm_distrib :=
  begin -- Ideal multiplication is distributive from the left!
   intros w y z,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hx,
     specialize hx ((w ⨂ y) ⨁ (w ⨂ z)), -- we proceed by showing that, for all x' ∈ w, for all
     apply hx,                             -- y' ∈ (y ⨁ z), x' * y' ∈ (w ⨂ y) ⨁ (w ⨂ z) 
     intros x' y' hx' hy',
     cases hy' with x'' hy',
     cases hy' with y'' hy',
     cases hy' with hx'' hy', -- we have that, for some x'' ∈ y, for some y'' ∈ z, y' = x'' + y''
     cases hy' with hy'' hy',
     have h : x' * y' = (x' * x'') + (x' * y''),
     { calc
        x' * y'     = x' * x'' + y'' : by rw hy'
                ... = (x' * x'') + x' * y'' : by exact left_distributivity x' x'' y'', },
     rw h,
     existsi x' * x'', -- to show that a sum is in a sum Ideal, we can show that its first term is
     existsi x' * y'', -- in the first Ideal, and it's second in the second Ideal
     split,
     { intros I hI,
       specialize hI x' x'',
       apply hI,
       { exact hx', },
       { exact hx'', }, },
     { split,
       { intros I hI,
         specialize hI x' y'',
         apply hI,
         { exact hx', },
         { exact hy'', }, },
       { exact rfl, }, }, },
   { intro hx,
     cases hx with x' hx,   -- because x is an element a sum Ideal, it itself can be written as a
     cases hx with y' hx,   -- sum, and we can prove that a sum is an element of an Ideal by 
     cases hx with hx' hx,  -- proving that each one of its terms is an element of the Ideal
     cases hx with hy' hx,
     specialize hx' (w ⨂ y ⨁ z),
     specialize hy' (w ⨂ y ⨁ z),
     rw hx,
     apply (subgroup_under_addition(w ⨂ y ⨁ z)).2.1 x' y',
     { apply hx', -- all elements in the mult_set of w and y contain x'
       intros x'' y'' hx'' hy'' I hI,
       apply hI,
       { exact hx'' },
       { existsi y'',
         existsi zero,
         split,
         { exact hy'' },
         { split,
           { exact zero_mem_Ideal z, },
           { calc
              y''     = y'' + zero : by { symmetry, exact zero_plus_neutral y'', }, }, }, }, },
     { apply hy', -- similarly for y'
       intros x'' y'' hx'' hy'' I hI,
       apply hI,
       { exact hx'', },
       { existsi zero,
         existsi y'',
         split,
         { exact zero_mem_Ideal y, },
         { split,
           { exact hy'', },
           { calc
              y''     = y'' + zero : by { symmetry, exact zero_plus_neutral y'' }
                  ... = zero + y'' : by exact plus_comm y'' zero, }, }, }, }, },
  end,
  rm_distrib :=
  begin -- Ideal multiplication is distributive from the right!
   -- this proof is substantially the same as the one above
   intros w y z,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hx,
     specialize hx ((w ⨂ z) ⨁ (y ⨂ z)),
     apply hx,
     intros x' y' hx' hy',
     cases hx' with x'' hx',
     cases hx' with y'' hx',
     cases hx' with hx'' hx',
     cases hx' with hy'' hx',
     have h : x' * y' = (x'' * y') + (y'' * y'),
     { calc
        x' * y'     = (x'' + y'') * y' : by rw hx'
                ... = (x'' * y') + y'' * y' : by exact right_distributivity x'' y'' y' },
     rw h,
     existsi (x'' * y'),
     existsi (y'' * y'),
     split,
     { intros I hI,
       apply hI x'' y',
       { exact hx'', },
       { exact hy', }, },
     { split,
       { intros I hI,
         apply hI y'' y',
         { exact hy'', },
         { exact hy', }, },
       { exact rfl, }, }, },
   { intro hx,
     cases hx with x' hx,
     cases hx with y' hx,
     cases hx with hx' hx,
     cases hx with hy' hx,
     specialize hx' ((w ⨁ y) ⨂ z),
     specialize hy' ((w ⨁ y) ⨂ z),
     rw hx,
     apply (subgroup_under_addition ((w ⨁ y) ⨂ z)).2.1,
     { apply hx',
       intros x'' y'' hx'' hy'' I hI,
       apply hI,
       { existsi x'',
         existsi zero,
         split,
         { exact hx'', },
         { split,
           { exact zero_mem_Ideal y, },
           { calc
              x'' = x'' + zero : by { symmetry, exact zero_plus_neutral x'', }, }, }, },
       { exact hy'' }, },
     { apply hy',
       intros x'' y'' hx'' hy'' I hI,
       apply hI,
       { existsi zero,
         existsi x'',
         split,
         { exact zero_mem_Ideal w, },
         { split,
           { exact hx'', },
           { calc
              x''     = x'' + zero : by { symmetry, exact zero_plus_neutral x'' }
                  ... = zero + x'' : by exact plus_comm x'' zero, }, }, },
       { exact hy'', }, }, },
  end,
  zero_lanni :=
  begin -- zero Ideal annihilates in multiplication from the left!
   intro w,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hx, -- first we prove that if x ∈ Ideal_zero ⨂ w then x ∈ Ideal_zero, this is easy,
     exact hx Ideal_zero (mult_set_self_left Ideal_zero w), }, -- since the antecedant implies 
                                                               -- that x is in all elements of the
                                                               -- the mult_set of Ideal_zero and
                                                               -- w, which includes Ideal_zero.
   { intro hx, -- next we prove that if x ∈ Ideal_zero, then x ∈ Ideal_zero ⨂ w, again easy,
     have h : x = zero, -- since the antecedant implies that x = zero, and all Ideals contain zero
     { exact hx },
     rw h,
     exact zero_mem_Ideal (Ideal_zero ⨂ w), },
  end,
  zero_ranni :=
  begin -- zero Ideal annihilates in multiplication from the right!
   -- this proof is substantially the same as the above.
   intro w,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hx,
     exact hx Ideal_zero (mult_set_self_right Ideal_zero w), },
   { intro hx,
     have h : x = zero,
     { exact hx, },
     rw h,
     exact zero_mem_Ideal (w ⨂ Ideal_zero), },
  end,
  plus_idemp :=
  begin -- Ideal addition is idempotent!
   intro x,
   apply ideal_equality_condition,
   funext,
   apply propext,
   split,
   { intro hz, -- if z ∈  x ⨁ x, then there is an x' ∈ x and a y ∈ x st. z = x' + y', and then
     cases hz with x' hz, -- we must have z ∈ x, since Ideals are closed under addition.
     cases hz with y' hz,
     cases hz with hx' hz,
     cases hz with hy' hz,
     rw hz,
     exact (subgroup_under_addition x).2.1 x' y' hx' hy', },
   { intro hz, -- conversely if z ∈ x then there exists an element of x and an element of x st.
     existsi z, -- their sum is z, namely z itself, and zero.
     existsi zero,
     split,
     { exact hz, },
     { split,
       { exact zero_mem_Ideal x, },
       { calc
          z = z + zero : by { symmetry, exact zero_plus_neutral z, }, }, }, },
  end } -- Ring Ideals form an Idempotent Semiring.
