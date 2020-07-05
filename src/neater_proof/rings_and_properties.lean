universe u

/-- Well-known definition of Rings, found e.g. here: 
    https://en.wikipedia.org/wiki/Ring_(mathematics)
    i've chosen to include the axioms altogether in one block, this doesn't make too much of a
    difference for how i use my rings, i'll do a similar thing when defining Ideals, but make the
    other choice, to include each axiom seperately, when defining Semi-Rings -/
structure Ring :=
(R : Type u)
(ring_struct : (R → R → R) × (R → R → R) × R × R)
(plus_assoc : ∀ x y z : R, ring_struct.1 x (ring_struct.1 y z) 
                         = ring_struct.1 (ring_struct.1 x y) z)
(plus_comm  : ∀ x y : R, ring_struct.1 x y = ring_struct.1 y x)
(plus_iden  : ∀ x : R, ring_struct.1 x ring_struct.2.2.1 = x)
(plus_inv   : ∀ x : R, ∃ x' : R, ring_struct.1 x x' = ring_struct.2.2.1)
(mult_assoc : ∀ x y z : R, ring_struct.2.1 x (ring_struct.2.1 y z) 
                         = ring_struct.2.1 (ring_struct.2.1 x y) z)
(mult_riden : ∀ x : R, ring_struct.2.1 x ring_struct.2.2.2 = x)
(mult_liden : ∀ x : R, ring_struct.2.1 ring_struct.2.2.2 x = x)
(left_distributivity : ∀ x y z : R, ring_struct.2.1 x (ring_struct.1 y z) 
                                  = ring_struct.1 (ring_struct.2.1 x y) (ring_struct.2.1 x z))
(right_distributivity : ∀ x y z : R, ring_struct.2.1 (ring_struct.1 x y) z 
                                   = ring_struct.1 (ring_struct.2.1 x z) (ring_struct.2.1 y z))

-- it's because of the following definitions and lemmas that i can use rings in a natural way

def plus {R : Ring} :=
R.ring_struct.1
local infixr ` + ` : 80 := plus

def mult {R : Ring} :=
R.ring_struct.2.1
local infixr ` * ` : 80 := mult

def zero {R : Ring} :=
R.ring_struct.2.2.1

def one {R : Ring} :=
R.ring_struct.2.2.2

def plus_assoc {R : Ring} : ∀ x y z : R.R, x + y + z = (x + y) + z :=
R.plus_assoc

def plus_comm {R : Ring} : ∀ x y : R.R, x + y = y + x :=
R.plus_comm

def plus_inv {R : Ring} : ∀ x : R.R, ∃ x' : R.R, x + x' = zero :=
R.plus_inv

def zero_plus_neutral {R : Ring} : ∀ x : R.R, x + zero = x :=
R.plus_iden

lemma zero_plus_neutral' {R : Ring} : ∀ x : R.R, x = x + zero :=
begin
 intro x,
 symmetry,
 exact zero_plus_neutral x,
end

def mult_assoc {R : Ring} : ∀ x y z : R.R, x * y * z = (x * y) * z :=
R.mult_assoc

def one_mult_neutral_right {R : Ring} : ∀ x : R.R, x * one = x :=
R.mult_riden

def one_mult_neutral_left {R : Ring} : ∀ x : R.R, one * x = x :=
R.mult_liden

def left_distributivity {R : Ring} : ∀ x y z : R.R, x * (y + z) = (x * y) + (x * z) :=
R.left_distributivity

def right_distributivity {R : Ring} : ∀ x y z : R.R, (x + y) * z = (x * z) + (y * z) :=
R.right_distributivity

lemma plus_inv_unique {R : Ring} : ∀ x y z : R.R, (x + y = zero ∧ x + z = zero) → y = z :=
begin
 intros x y z h,
 cases h with hy hz,
 calc
  y     = y + zero    : by exact zero_plus_neutral' y
    ... = y + x + z   : by rw hz
    ... = (y + x) + z : by rw plus_assoc y x z
    ... = (x + y) + z : by rw plus_comm y x
    ... = zero + z    : by rw hy
    ... = z + zero    : by exact plus_comm zero z
    ... = z           : by exact zero_plus_neutral z, 
end

lemma zero_annihilates_left {R : Ring} : ∀ x : R.R, zero * x = zero :=
begin
 intro x,
 symmetry,
 have h : zero * x = (zero * x) + (zero * x),
 {
  calc
   zero * x     = (zero + zero) * x       : by rw zero_plus_neutral zero
            ... = (zero * x) + (zero * x) : by exact right_distributivity zero zero x,
 },
 have h' : ∃ c : R.R, (zero * x) + c = zero,
 { exact plus_inv (zero * x), },
 cases h' with c hc,
 calc
  zero     = (zero * x) + c                : by { symmetry, exact hc }
       ... = ((zero * x) + (zero * x)) + c : by rw ← h
       ... = (zero * x) + ((zero * x) + c) : by rw plus_assoc (zero * x) (zero * x) c
       ... = (zero * x) + zero             : by rw hc
       ... = zero * x                      : by exact zero_plus_neutral (zero * x),
end

lemma zero_annihilates_right {R : Ring} : ∀ x : R.R, x * zero = zero :=
begin
 intro x,
 symmetry,
 have h : x * zero = (x * zero) + (x * zero),
 {
  calc
   x * zero     = x * zero + zero         : by rw zero_plus_neutral
            ... = (x * zero) + (x * zero) : by exact left_distributivity x zero zero, 
 },
 have h' : ∃ c : R.R, (x * zero) + c = zero,
 { exact plus_inv (x * zero), },
 cases h' with c hc,
 calc
  zero     = (x * zero) + c                : by { symmetry, exact hc }
       ... = ((x * zero) + (x * zero)) + c : by rw ← h
       ... = (x * zero) + ((x * zero) + c) : by rw plus_assoc (x * zero) (x * zero) c
       ... = (x * zero) + zero             : by rw hc
       ... = x * zero                      : by exact zero_plus_neutral (x * zero),
end

lemma negative_one {R : Ring} : ∀ x y : R.R, one + x = zero → y + x * y = zero :=
begin
 intros x y hx,
 have h : y = one * y,
 { symmetry,
   exact one_mult_neutral_left y, },
 calc
  y + x * y     = (one * y) + (x * y) : by rw ← h
            ... = (one + x) * y       : by { symmetry, exact right_distributivity one x y }
            ... = zero * y            : by rw hx
            ... = zero                : by exact zero_annihilates_left y,
end

