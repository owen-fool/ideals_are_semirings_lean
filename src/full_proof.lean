
universe u

structure Ring :=
  (R           : Type u)
  (ring_struct : (R → R → R) × (R → R → R) × R × R)
  (ring_axioms : ( (∀ (x y z : R), ring_struct.1 x (ring_struct.1 y z)
                                 = ring_struct.1 (ring_struct.1 x y) z)
                 ∧ (∀ (x y : R),   ring_struct.1 x y = ring_struct.1 y x)
                 ∧ (∀ (x : R),     ring_struct.1 x ring_struct.2.2.1
                                 = x)
                 ∧ (∀ (x : R), 
                    ∃ (x' : R),    ring_struct.1 x x'
                                 = ring_struct.2.2.1))
                 ∧ 
                (( (∀ (x y z : R), ring_struct.2.1 x (ring_struct.2.1 y z)
                                 = ring_struct.2.1 (ring_struct.2.1 x y) z)
                 ∧ (∀ (x : R),     ring_struct.2.1 x ring_struct.2.2.2
                                 = x)
                 ∧ (∀ (x : R),     ring_struct.2.1 ring_struct.2.2.2 x
                                 = x))
                 ∧
                 ( (∀ (x y z : R), ring_struct.2.1 x (ring_struct.1 y z)
                                 = ring_struct.1 (ring_struct.2.1 x y)
                                                 (ring_struct.2.1 x z))
                 ∧ (∀ (x y z : R), ring_struct.2.1 (ring_struct.1 x y) z
                                 = ring_struct.1 (ring_struct.2.1 x z)
                                                 (ring_struct.2.1 y z)))))
                                                 
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

def group_under_addition {R : Ring} :=
  R.ring_axioms.1

def monoid_under_multiplication {R : Ring} :=
  R.ring_axioms.2.1

def distributivity_laws {R : Ring} :=
  R.ring_axioms.2.2

structure Ideal (R : Ring) :=
  (I : set R.R)
  (ideal_axioms : (   I zero 
                   ∧ (∀ (x y : R.R), I x → I y → I (x + y))
                   ∧ (∀ (x x' : R.R), (x + x') = zero 
                                     → I x → I x'))
                   ∧ 
                   ( (∀ (x y : R.R), I x → I (x * y))
                   ∧ (∀ (x y : R.R), I x → I (y * x))))

def subgroup_under_addition {R : Ring} (I : Ideal R) :=
  I.ideal_axioms.1

def multiplication_conditions {R : Ring} (I : Ideal R) :=
  I.ideal_axioms.2

def min_ideal {R : Ring} (IS : set (Ideal R)) : Ideal R :=
  {
   I := {x | ∀ (Id : Ideal R), Id ∈ IS → x ∈ Id.I}, 
   ideal_axioms := 
     begin
      split,
      split,
      intros Id hId,
      exact Id.ideal_axioms.1.1,
      split,
      intros x y hx hy,
      intros Id hId,
      specialize hx Id hId,
      specialize hy Id hId,
      exact Id.ideal_axioms.1.2.1 x y hx hy,
      intros x x' hxx' hx Id hId,
      specialize hx Id hId,
      exact Id.ideal_axioms.1.2.2 x x' hxx' hx,
      split,
      intros x y hx Id hId,
      specialize hx Id hId,
      exact Id.ideal_axioms.2.1 x y hx,
      intros x y hx Id hId,
      specialize hx Id hId,
      exact Id.ideal_axioms.2.2 x y hx,
     end
  }

def mult_set {R : Ring} (I I' : Ideal R) : set (Ideal R) :=
  {Id | ∀ (x y : R.R), x ∈ I.I → y ∈ I'.I → (x * y) ∈ Id.I}

def Ideal_mult {R : Ring} (I I' : Ideal R) : Ideal R :=
  min_ideal (mult_set I I')
local infixr ` ⨂ ` : 80 := Ideal_mult

lemma assoc_p {R : Ring} : ∀ (x y z : R.R), x + (y + z) = (x + y) + z :=
 begin
  intros x y z,
  exact group_under_addition.1 x y z, 
 end

lemma comm_p {R : Ring} : ∀ (x y : R.R), x + y = y + x :=
 begin
  intros x y,
  exact group_under_addition.2.1 x y,
 end

lemma inv_p {R : Ring} : ∀ (x : R.R), ∃ (x' : R.R), x + x' = zero :=
 begin
  intro x,
  exact group_under_addition.2.2.2 x,
 end

lemma newt_p_1 {R : Ring} : ∀ (x : R.R), x = x + zero :=
 begin
  intro x,
  symmetry,
  exact group_under_addition.2.2.1 x,
 end

lemma inv_unique {R : Ring} : ∀ (x y z : R.R), ((x + y = zero) ∧ (x + z = zero)) → y = z :=
 begin
  intros x y z h,
  cases h with hy hz,
  calc
   y     = y + zero : by exact newt_p_1 y
     ... = y + (x + z) : by rw hz
     ... = y + x + z : by rw assoc_p y x z
     ... = (y + x) + z : by rw ← assoc_p y x z
     ... = (x + y) + z : by rw comm_p y x
     ... = zero + z : by rw ← hy
     ... = z + zero : by exact comm_p zero z
     ... = z : by { symmetry, exact newt_p_1 z },
 end

def Ideal_plus {R : Ring} (I I' : Ideal R) : Ideal R :=
  {
   I := {z | ∃ (x y : R.R), x ∈ I.I ∧ y ∈ I'.I ∧ z = x + y},
   ideal_axioms :=
    begin
     split,
     split,
     existsi zero,
     existsi zero,
     split,
     exact I.ideal_axioms.1.1,
     split,
     exact I'.ideal_axioms.1.1,
     symmetry,
     exact group_under_addition.2.2.1 zero,
     split,
     intros x y hx hy,
     cases hx with x' hx,
     cases hx with y' hx,
     cases hy with x'' hy,
     cases hy with y'' hy,
     cases hx with hx' hx,
     cases hx with hy' hx,
     cases hy with hx'' hy,
     cases hy with hy'' hy,
     existsi (x' + x''),
     existsi (y' + y''),
     split,
     exact I.ideal_axioms.1.2.1 x' x'' hx' hx'',
     split,
     exact I'.ideal_axioms.1.2.1 y' y'' hy' hy'',
     rw hx,
     rw hy,
     rw ← assoc_p,
     rw assoc_p y' x'' y'',
     rw comm_p y' x'',
     rw ← assoc_p x'' y' y'',
     rw assoc_p,
     intros x x' hxx' hx,
     cases hx with y hx,
     cases hx with y' hx,
     cases hx with hy hx,
     cases hx with hy' hx,
     have H : ∃ (a : R.R), y + a = zero,
     exact inv_p y,
     cases H with a Ha,
     have H : ∃ (a' : R.R), y' + a' = zero,
     exact inv_p y',
     cases H with a' Ha',
     have H : x + (a + a') = zero,
     rw hx,
     rw ← assoc_p,
     rw comm_p a a',
     rw assoc_p y' a' a,
     rw Ha',
     rw assoc_p,
     rw ← newt_p_1 y,
     exact Ha,
     have H' : x' = (a + a'),
     apply inv_unique x,
     split,
     exact hxx',
     exact H,
     existsi a,
     existsi a',
     split,
     exact (subgroup_under_addition I).2.2 y a Ha hy,
     split,
     exact (subgroup_under_addition I').2.2 y' a' Ha' hy',
     exact H',
     split,
     intros x y hx,
     cases hx with x' hx,
     cases hx with y' hx,
     cases hx with hx' hx,
     cases hx with hy' hx,
     existsi (x' * y),
     existsi (y' * y),
     split,
     exact (multiplication_conditions I).1 x' y hx',
     split,
     exact (multiplication_conditions I').1 y' y hy',
     rw hx,
     exact distributivity_laws.2 x' y' y,
     intros x y hx,
     cases hx with x' hx,
     cases hx with y' hx,
     cases hx with hx' hx,
     cases hx with hy' hx,
     existsi (y * x'),
     existsi (y * y'),
     split,
     exact (multiplication_conditions I).2 x' y hx',
     split,
     exact (multiplication_conditions I').2 y' y hy',
     rw hx,
     exact distributivity_laws.1 y x' y',
    end
  }
local infixr ` ⨁ ` : 80 := Ideal_plus
 -- next, want to define is_semiring property!

structure is_semiring (X : Type u) :=
  (plus : X → X → X)
  (mult : X → X → X)
  (zero' : X)
  (one'  : X)
  (plus_assoc : ∀ (x y z : X), plus x (plus y z) = plus (plus x y) z)
  (plus_comm  : ∀ (x y : X),   plus x y = plus y x)
  (plus_ident : ∀ (x : X),     plus x zero' = x)
  (mult_assoc : ∀ (x y z : X), mult x (mult y z) = mult (mult x y) z)
  (mult_liden : ∀ (x : X),     mult one' x = x)
  (mult_riden : ∀ (x : X),     mult x one' = x)
  (lm_distrib : ∀ (x y z : X), mult x (plus y z) = plus (mult x y) (mult x z))
  (rm_distrib : ∀ (x y z : X), mult (plus x y) z = plus (mult x z) (mult y z))
  (zero_lanni : ∀ (x : X),     mult zero' x = zero')
  (zero_ranni : ∀ (x : X),     mult x zero' = zero')

-- let's gooo!

lemma distribby_l {R : Ring} : ∀ (x y z : R.R), x * (y + z) = (x * y) + (x * z) :=
 begin
  intros x y z,
  exact distributivity_laws.1 x y z,
 end

lemma distribby_r {R : Ring} : ∀ (x y z : R.R), (x + y) * z = (x * z) + (y * z) :=
 begin
  intros x y z,
  exact distributivity_laws.2 x y z,
 end

lemma zero_left_annihilates {R : Ring} : ∀ (x : R.R), (zero * x) = zero :=
 begin
  intro x,
  have t : zero * x = (zero * x) + (zero * x),
  {
   calc
    zero * x     = (zero + zero) * x : by rw ← newt_p_1 zero
             ... = (zero * x) + (zero * x) : by exact distribby_r zero zero x,
  },
  symmetry,  
  have t' : ∃ (c : R.R), (zero * x) + c = zero,
  { exact inv_p (zero * x), },
  cases t' with c hc,
  calc
   zero     = (zero * x) + c : by { symmetry, exact hc }
        ... = ((zero * x) + (zero * x)) + c : by rw ← t
        ... = (zero * x) + ((zero * x) + c) : by rw assoc_p (zero * x) (zero * x) c
        ... = (zero * x) + zero             : by rw hc
        ... = (zero * x)                    : by { symmetry, exact newt_p_1 (zero * x) },
 end

lemma zero_right_annihilates {R : Ring} : ∀ (x : R.R), (x * zero) = zero :=
 begin
  intro x,
  have t : x * zero = (x * zero) + (x * zero),
  {
   calc
    x * zero     = x * (zero + zero) : by rw ← newt_p_1 zero
             ... = (x * zero) + (x * zero) : by exact distribby_l x zero zero,
  },
  symmetry,
  have t' : ∃ (c : R.R), (x * zero) + c = zero,
  { exact inv_p (x * zero), },
  cases t' with c hc,
  calc
   zero     = (x * zero) + c : by { symmetry, exact hc }
        ... = ((x * zero) + (x * zero)) + c : by rw ← t
        ... = (x * zero) + ((x * zero) + c) : by rw assoc_p (x * zero) (x * zero) c
        ... = (x * zero) + zero             : by rw hc
        ... = (x * zero)                    : by { symmetry, exact newt_p_1 (x * zero) },
 end

def Ideal_zero (R : Ring) : Ideal R :=
  {
            I := {x | x = zero},
            ideal_axioms := 
             begin
              split, 
              split,
              exact rfl,
              split,
              intros x y hx hy,
              have t : x = zero,
              exact hx, 
              rw t,
              have t' : y = zero, 
              exact hy,
              rw t',
              rw ← newt_p_1 zero,
              exact rfl,
              intros x x' hxx' hx,
              have k : x = zero,
              exact hx,
              rw k at hxx',
              rw comm_p zero x' at hxx',
              rw ← newt_p_1 x' at hxx',
              exact hxx',
              split,
              intros x y hx,
              have H : x = zero,
              exact hx,
              rw H,
              rw zero_left_annihilates y,
              exact rfl,
              intros x y hx,
              have h : x = zero,
              exact hx,
              rw h,
              rw zero_right_annihilates y,
              exact rfl,
             end
           }

lemma s {R : Ring} : ∀ (x : R.R), x ∈ (Ideal_zero R).I → x = zero :=
 begin
  intros x hx,
  exact hx,
 end 

lemma ideal_equality_condition {R : Ring} : ∀ (I I' : Ideal R), I.I = I'.I → I = I' :=
 begin
  intros I I' h,
  have t : (I.I zero ∧ (∀ (x y : R.R), I.I x → I.I y → I.I (x + y))
                   ∧ (∀ (x x' : R.R), (x + x') = zero → I.I x → I.I x'))
                   ∧ 
                   ((∀ (x y : R.R), I.I x → I.I (x * y))
                   ∧ (∀ (x y : R.R), I.I x → I.I (y * x))) 
           ↔
           (I'.I zero ∧ (∀ (x y : R.R), x ∈ I'.I → I'.I y → I'.I (x + y))
                   ∧ (∀ (x x' : R.R), (x + x') = zero → I'.I x → I'.I x'))
                   ∧ 
                   ((∀ (x y : R.R), I'.I x → I'.I (x * y))
                   ∧ (∀ (x y : R.R), I'.I x → I'.I (y * x))),
  split,
  intro H,
  rw ← h,
  exact H,
  intro H,
  rw h,
  exact H,
  have t' : ((I.I zero ∧ (∀ (x y : R.R), I.I x → I.I y → I.I (x + y))
                   ∧ (∀ (x x' : R.R), (x + x') = zero → I.I x → I.I x'))
                   ∧ 
                   ((∀ (x y : R.R), I.I x → I.I (x * y))
                   ∧ (∀ (x y : R.R), I.I x → I.I (y * x))))
           =
           ((I'.I zero ∧ (∀ (x y : R.R), x ∈ I'.I → I'.I y → I'.I (x + y))
                   ∧ (∀ (x x' : R.R), (x + x') = zero → I'.I x → I'.I x'))
                   ∧ 
                   ((∀ (x y : R.R), I'.I x → I'.I (x * y))
                   ∧ (∀ (x y : R.R), I'.I x → I'.I (y * x)))),
  apply propext,
  exact t,
  cases I, -- had to search through zulip chat to finish proof of this lemma from here
  cases I', -- all credit to Kenny Lau message in new members 12.11 pm 23rd May
  congr,   -- i think that possibly i've defined ideals in an overcomplicated way, with the axioms
  exact h, -- all as one block, but possibly doing it differently would have meant more congr-ing
 end

def Ideal_one {R : Ring} : Ideal R :=
  {
   I := λ x, true,
   ideal_axioms := 
    begin
     simp,
     intros x x',
     cc, 
    end
  }

lemma self_mult_set {R : Ring} (I : Ideal R) : ∀ (I' : Ideal R), I ∈ (mult_set I I') :=
 begin
  intro I',
  intros x y hx hy,
  exact (multiplication_conditions I).1 x y hx,
 end

lemma self_mult_set' {R : Ring} (I : Ideal R) : ∀ (I' : Ideal R), I ∈ (mult_set I' I) :=
 begin
  intro I',
  intros x y hx hy,
  exact (multiplication_conditions I).2 y x hy,
 end

lemma newt_m_r {R : Ring} : ∀ (x : R.R), (x * one) = x :=
 begin
  intro x,
  exact monoid_under_multiplication.2.1 x,
 end

lemma newt_m_l {R : Ring} : ∀ (x : R.R), (one * x) = x :=
 begin
  intro x,
  exact monoid_under_multiplication.2.2 x,
 end

lemma Ideal_has_zero {R : Ring} : ∀ (I : Ideal R), zero ∈ I.I :=
 begin
  intro I,
  exact (subgroup_under_addition I).1,
 end

def sum_num {R : Ring} (f : ℕ → R.R) : ℕ → R.R
 | 0 := f 0
 | (nat.succ n) := (f (nat.succ n)) + (sum_num n)

def sum_sum_num {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) : ℕ → R.R
 | 0 := fx 0
 | (nat.succ n) := if n < nx then (fx (nat.succ n) + sum_num fx n)
                   else (fy (nat.succ n - nat.succ nx) + sum_sum_num n)

lemma silly : ∀ n : ℕ, ¬ n < n :=
begin
 intro n,
 induction n with n hn,
 intro hz,
 cases hz with r hr,
 intro h,
 apply hn,
 have t : nat.add n 1 < nat.add n 1,
 exact h,
 exact nat.lt_of_succ_lt_succ h,
end

lemma hateful {R : Ring} (fx fy : ℕ → R.R) : ∀ n : ℕ, sum_sum_num n fx fy n = sum_num fx n :=
 begin
  intro n,
  induction n with n hn,
  exact rfl,
  have t : n < nat.succ n,
  exact nat.lt_succ_self n,
  have t' : sum_sum_num (nat.succ n) fx fy (nat.succ n) = ite (n < nat.succ n) (fx (nat.succ n) + sum_num fx n) (fy (nat.succ n - nat.succ (nat.succ n)) + sum_sum_num (nat.succ n) fx fy n),
  exact rfl,
  have t'' : sum_sum_num (nat.succ n) fx fy (nat.succ n) = fx (nat.succ n) + sum_num fx n,
  simp [t, t'],
  rw t'',
  exact rfl,
 end

lemma add_succ_commute : ∀ (m n : ℕ), nat.add m (nat.succ n) = nat.succ (nat.add m n) :=
begin
 intros m n,
 exact rfl,
end

lemma add_succ_commute' : ∀ (m n : ℕ), nat.add (nat.succ m) n = nat.succ (nat.add m n) :=
begin
 intros m n,
 exact nat.succ_add m n, 
end

lemma nexting : ∀ (m n : ℕ), m < nat.succ (nat.add m n) :=
begin
 intros m n,
 apply nat.lt_succ_of_le,
 induction n with n hn,
 have t : nat.add m 0 = m,
 exact nat.add_zero m,
 apply nat.le_of_eq,
 rw t,
 rw add_succ_commute m n,
 apply nat.le_of_lt,
 apply nat.lt_succ_of_le,
 exact hn,
end

lemma nexting' : ∀ (m n : ℕ), ¬ nat.succ (nat.add m n) < m :=
begin
 intros m n h,
 have h' := nexting m n,
 have h'' := silly m,
 apply h'',
 exact nat.lt_trans h' h,
end

lemma snarl : ∀ (m n : ℕ), nat.succ (nat.add m n) - m = nat.succ n :=
begin
 intros m n,
 induction n with n hn,
 have t : nat.add m 0 = m,
 exact nat.add_zero m,
 rw t,
 have t' : 1 = nat.succ (m - m),
 rw nat.sub_self m,
 rw nat.succ_sub,
 symmetry,
 exact t',
 apply le_of_eq,
 exact rfl,
 rw add_succ_commute m n,
 rw ← hn,
 apply nat.succ_sub,
 apply nat.le_of_lt,
 exact nexting m n,
end

lemma sum_sum_num_is_sum {R : Ring} (nx ny : ℕ) (fx fy : ℕ → R.R) :
  (sum_sum_num nx fx fy) (nat.succ (nat.add nx ny)) = (sum_num fx nx) + (sum_num fy ny) :=
  begin
   induction ny with ny indhy,
   have t : nat.add nx 0 = nx,
   { exact nat.add_zero nx, },
   rw t,
   have t' : sum_sum_num nx fx fy (nat.succ nx) = ite (nx < nx) (fx (nat.succ nx) + sum_num fx nx) (fy (nat.succ nx - nat.succ nx) + sum_sum_num nx fx fy nx),
   exact rfl,
   have t'' : ¬ nx < nx,
   exact silly nx,
   have t''' : sum_sum_num nx fx fy (nat.succ nx) = fy (nat.succ nx - nat.succ nx) + sum_sum_num nx fx fy nx,
   simp [t', t''],
   rw t''',
   have t'''' : nat.succ nx - nat.succ nx = 0,
   simp,
   exact nat.sub_self nx,
   rw t'''',
   rw comm_p,
   rw hateful fx fy nx,
   exact rfl,
   rw add_succ_commute nx ny,
   have t := nexting' nx ny,
   have t' : sum_sum_num nx fx fy (nat.succ (nat.succ (nat.add nx ny))) = ite (nat.succ (nat.add nx ny) < nx) (fx (nat.succ (nat.succ (nat.add nx ny))) + sum_num fx (nat.succ (nat.add nx ny))) (fy (nat.succ (nat.succ (nat.add nx ny)) - nat.succ nx) + sum_sum_num nx fx fy (nat.succ (nat.add nx ny))),
   exact rfl,
   simp [t, t'],
   rw indhy,
   rw snarl nx ny,
   rw comm_p (sum_num fx nx) (sum_num fy ny),
   rw comm_p (sum_num fx nx) (sum_num fy (nat.succ ny)),
   rw assoc_p,
   exact rfl,
  end

def sum_fun {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) : ℕ → R.R 
 | 0 := fx 0
 | (nat.succ n) := if n < nx then fx (nat.succ n)
                   else fy (nat.succ n - nat.succ nx)

lemma simple_decidability : ∀ m n : ℕ, n < m ∨ ¬ (n < m) :=
begin
 intros m n,
 have t : n ≤ m ∨ m ≤ n,
 exact nat.le_total,
 cases t,
 have t' : n = m ∨ n < m,
 exact nat.eq_or_lt_of_le t,
 cases t',
 right,
 rw t',
 exact nat.lt_irrefl m,
 left,
 exact t',
 right,
 have t' : m = n ∨ m < n,
 exact nat.eq_or_lt_of_le t,
 cases t',
 rw t',
 exact nat.lt_irrefl n,
 intro h,
 apply nat.lt_irrefl m,
 exact nat.lt_trans t' h,
end

lemma sum_fxes {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) :
∀ n : ℕ, (n < nx) → sum_sum_num nx fx fy n = sum_num fx n :=
begin
 intros n hn,
 induction n with n indh,
 exact rfl,
 have t : n < nx,
 apply nat.lt_of_succ_lt,
 exact hn,
 specialize indh t,
 have t' : sum_sum_num nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n) + sum_num fx n) (fy (nat.succ n - nat.succ nx) + sum_sum_num nx fx fy n),
 exact rfl,
 have t'' : sum_sum_num nx fx fy (nat.succ n) = fx (nat.succ n) + sum_num fx n,
 simp [t, t'],
 rw t'',
 exact rfl,
end

lemma sum_proof {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) : 
∀ (n : ℕ), (sum_num (sum_fun nx fx fy) n = sum_sum_num nx fx fy n) :=
begin
 intro n,
 induction n with n indh,
 exact rfl,
 have hn : (n < nx) ∨ ¬ (n < nx),
 exact simple_decidability nx n,
 cases hn,
 have t : sum_num (sum_fun nx fx fy) (nat.succ n) = (sum_fun nx fx fy (nat.succ n)) + (sum_num (sum_fun nx fx fy) n),
 exact rfl,
 rw t,
 have t' : sum_fun nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n)) (fy (nat.succ n - nat.succ nx)),
 exact rfl,
 have t'' : sum_fun nx fx fy (nat.succ n) = fx (nat.succ n),
 simp [t', hn],
 rw t'',
 rw indh,
 rw sum_fxes nx fx fy n,
 have h : sum_sum_num nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n) + sum_num fx n) (fy (nat.succ n - nat.succ nx) + (sum_sum_num nx fx fy n)),
 exact rfl,
 have h' : sum_sum_num nx fx fy (nat.succ n) = fx (nat.succ n) + sum_num fx n,
 simp [hn, h],
 rw h',
 exact hn,
 have t : sum_num (sum_fun nx fx fy) (nat.succ n) = (sum_fun nx fx fy (nat.succ n)) + sum_num (sum_fun nx fx fy) n,
 exact rfl,
 rw t,
 have h : sum_sum_num nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n) + sum_num fx n) (fy (nat.succ n - nat.succ nx) + sum_sum_num nx fx fy n),
 exact rfl,
 have h' : sum_sum_num nx fx fy (nat.succ n) = fy (nat.succ n - nat.succ nx) + sum_sum_num nx fx fy n,
 simp [hn, h],
 rw h',
 have t' : sum_fun nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n)) (fy (nat.succ n - nat.succ nx)),
 exact rfl,
 have t'' : sum_fun nx fx fy (nat.succ n) = fy (nat.succ n - nat.succ nx),
 simp [hn, t'],
 rw t'',
 rw indh,
end

lemma assoc_m {R : Ring} : ∀ x y z : R.R, x * y * z = (x * y) * z :=
begin
 intros x y z,
 exact monoid_under_multiplication.1 x y z,
end

lemma negative_one {R : Ring} : ∀ x y : R.R, one + x = zero → (y + (x * y) = zero) :=
begin
 intros x y hx,
 have t : y = one * y,
 symmetry,
 exact newt_m_l y,
 rw t,
 rw assoc_m,
 rw newt_m_r x,
 rw ← distribby_r,
 rw hx,
 rw zero_left_annihilates y, 
end

def mul_fun {R : Ring} (m : R.R) (f : ℕ → R.R) : ℕ → R.R :=
 λ n, (m * (f n))

def mul_fun' {R : Ring} (m : R.R) (f : ℕ → R.R) : ℕ → R.R :=
 λ n, ((f n) * m)

lemma mul_proof {R : Ring} (y : R.R) (f : ℕ → R.R) :
 ∀ n : ℕ, y * (sum_num f n) = sum_num (mul_fun y f) n :=
 begin
  intro n,
  induction n with n hn,
  exact rfl,
  have t : sum_num (mul_fun y f) (nat.succ n) = mul_fun y f (nat.succ n) + (sum_num (mul_fun y f) n),
  exact rfl,
  rw t,
  rw ← hn,
  have t' : mul_fun y f (nat.succ n) = y * f (nat.succ n),
  exact rfl,
  rw t',
  rw ← distribby_l y (f (nat.succ n)) (sum_num f n),
  exact rfl, 
 end

lemma mul_proof' {R : Ring} (y : R.R) (f : ℕ → R.R) :
 ∀ n : ℕ, (sum_num f n) * y = sum_num (mul_fun' y f) n :=
 begin
  intro n,
  induction n with n hn,
  exact rfl,
  have t : sum_num (mul_fun' y f) (nat.succ n) = mul_fun' y f (nat.succ n) + (sum_num (mul_fun' y f) n),
  exact rfl,
  rw t,
  rw ← hn,
  have t' : mul_fun' y f (nat.succ n) = (f (nat.succ n)) * y,
  exact rfl,
  rw t',
  rw ← distribby_r,
  exact rfl,
 end

def set_num {R : Ring} (X : set R.R) (H : ∃ x : R.R, x ∈ X) : Ideal R :=
 { 
  I := {p | ∃ n : ℕ, ∃ f : ℕ → R.R, (p = (sum_num f n) ∧ 
                                      (∀ n : ℕ, ∃ x ∈ X, ∃ y z : R.R, 
                                       f n = y * x * z))},
  ideal_axioms :=
   begin
    split,
    split,
    existsi 0,
    cases H with x H,
    existsi λ n, zero * x,
    split,
    rw zero_left_annihilates,
    refl,
    intro n,
    existsi x,
    existsi H,
    existsi zero,
    existsi zero,
    rw zero_right_annihilates x,
    rw zero_left_annihilates,
    rw zero_left_annihilates zero,
    split,
    intros x y,
    intros hx hy,
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    cases hy with ny hy,
    cases hy with fy hy,
    cases hy with eqy hy,
    existsi nat.succ (nat.add nx ny),
    existsi sum_fun nx fx fy,
    split,
    rw eqx,
    rw eqy,
    symmetry,
    rw sum_proof nx fx fy (nat.succ (nat.add nx ny)), 
    exact sum_sum_num_is_sum nx ny fx fy,
    intro n,
    induction n with n indh,
    specialize hx 0,
    cases hx with x hx,
    cases hx with H hx,
    cases hx with y hx,
    existsi x,
    existsi H,
    existsi y,
    exact hx,
    have dec := simple_decidability nx n,
    have t : sum_fun nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n)) (fy (nat.succ n - nat.succ nx)),
    exact rfl,
    cases dec,
    have t' : sum_fun nx fx fy (nat.succ n) = fx (nat.succ n),
    simp [t, dec],
    rw t',
    specialize hx (nat.succ n),
    exact hx,
    have t' : sum_fun nx fx fy (nat.succ n) = fy (nat.succ n - nat.succ nx),
    simp [t, dec],
    rw t',
    specialize hy (nat.succ n - nat.succ nx),
    exact hy,
    intros x x' hxx' hx,
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    existsi nx,
    have none : ∃ o : R.R, one + o = zero,
    exact inv_p one,
    cases none with o none,
    existsi mul_fun o fx,
    split,
    rw ← mul_proof o fx nx,
    apply inv_unique x,
    split,
    exact hxx',
    rw eqx,
    apply negative_one,
    exact none,
    intro n,
    specialize hx n,
    have t : mul_fun o fx n = o * (fx n),
    exact rfl,
    rw t,
    cases hx with x'' hx,
    cases hx with H hx,
    cases hx with y hx,
    cases hx with z hx,
    existsi x'',
    existsi H,
    existsi o * y,
    existsi z,
    rw ← assoc_m,
    rw ← hx,
    split,
    intros x y hx,
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    existsi nx,
    existsi mul_fun' y fx,
    split,
    rw eqx,
    exact mul_proof' y fx nx,
    intro n,
    specialize hx n,
    have t : mul_fun' y fx n = (fx n) * y,
    exact rfl,
    rw t,
    cases hx with x' hx,
    cases hx with H hx,
    cases hx with y' hx, 
    cases hx with z hx,
    existsi x',
    existsi H,
    existsi y',
    existsi z * y,
    rw assoc_m x' z y,
    rw assoc_m y' (x' * z) y,
    rw hx,
    intros x y hx,
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    existsi nx,
    existsi mul_fun y fx,
    split,
    rw eqx,
    exact mul_proof y fx nx,
    intro n,
    specialize hx n,
    cases hx with x' hx,
    cases hx with H' hx,
    cases hx with y' hx,
    cases hx with z hx,
    existsi x',
    existsi H',
    have t : mul_fun y fx n = y * (fx n),
    exact rfl,
    rw t,
    existsi y * y',
    existsi z,
    rw ← assoc_m y y' (x' * z),
    rw hx,
   end, 
 }

lemma set_num_inclusion {R : Ring} (X : set R.R) (H : (∃ (x' : R.R), x' ∈ X)) : 
 ∀ x : R.R, x ∈ X → x ∈ (set_num X H).I :=
begin
 intros x hx,
 existsi 0,
 existsi λ n, x,
 split,
 exact rfl,
 intro n,
 existsi x,
 existsi hx,
 existsi one,
 existsi one,
 have t : (λ (n : ℕ), x) n = x,
 exact rfl,
 rw t,
 rw newt_m_r,
 rw newt_m_l,
end

def set_mult {R : Ring} (I I' : Ideal R) : set R.R :=
 {z | ∃ x ∈ I.I, ∃ y ∈ I'.I, z = x * y}

lemma nonempty_set_mult {R : Ring} (I I' : Ideal R) : ∃ x : R.R, x ∈ set_mult I I' :=
begin
 existsi zero,
 existsi zero,
 existsi (subgroup_under_addition I).1,
 existsi zero,
 existsi (subgroup_under_addition I').1,
 rw zero_left_annihilates,
end

lemma set_mult_mult_set {R : Ring} (I I' : Ideal R) : 
 (set_num (set_mult I I') (nonempty_set_mult I I')) ∈ mult_set I I' :=
 begin
  intros x y hx hy,
  apply set_num_inclusion (set_mult I I') (nonempty_set_mult I I') (x * y),
  existsi x,
  existsi hx,
  existsi y,
  existsi hy,
  exact rfl,
 end

lemma fin_sum_member_condition {R : Ring} (I : Ideal R) (f : ℕ → R.R) (m : ℕ) :
(∀ n : ℕ, (f n) ∈ I.I) → (sum_num f m) ∈ I.I :=
begin
 intro hn,
 induction m with m indh,
 specialize hn 0,
 exact hn,
 have t : sum_num f (nat.succ m) = f (nat.succ m) + sum_num f m,
 exact rfl,
 rw t,
 apply (subgroup_under_addition I).2.1,
 exact hn (nat.succ m),
 exact indh,
end

theorem ideal_semirings {R : Ring} : is_semiring (Ideal R) :=
  {
   plus := Ideal_plus,
   mult := Ideal_mult,
   zero' := Ideal_zero R,
   one'  := Ideal_one,
   plus_assoc := 
   begin
    intros x y w,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hz,
    cases hz with x' hz,
    cases hz with y' hz,
    cases hz with hx' hz,
    cases hz with hy' hz,
    cases hy' with x'' hy',
    cases hy' with y'' hy',
    cases hy' with hx'' hy',
    cases hy' with hy'' hy',
    rw hy' at hz,
    existsi (x' + x''),
    existsi y'',
    split,
    existsi x',
    existsi x'',
    split,
    exact hx',
    split,
    exact hx'',
    exact rfl,
    simp [hy'', hz],
    exact assoc_p x' x'' y'',
    intro hz,
    cases hz with x' hz,
    cases hz with y' hz,
    cases hz with hx' hz,
    cases hz with hy' hz,
    cases hx' with x'' hx',
    cases hx' with y'' hx',
    cases hx' with hx'' hx',
    cases hx' with hy'' hx',
    rw hx' at hz,
    rw ← assoc_p at hz,
    existsi x'',
    existsi (y'' + y'),
    split,
    exact hx'',
    split,
    existsi y'',
    existsi y',
    simp [hy'', hy'],
    exact hz,
   end,
   plus_comm  := 
   begin
    intros x y,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hz,
    cases hz with x' hz,
    cases hz with y' hz,
    cases hz with hx' hz,
    cases hz with hy' hz,
    existsi y',
    existsi x',
    split,
    exact hy',
    split,
    exact hx',
    rw comm_p y' x',
    assumption,
    intro hz,
    cases hz with y' hz,
    cases hz with x' hz,
    cases hz with hy' hz,
    cases hz with hx' hz,
    existsi x',
    existsi y',
    split,
    exact hx',
    split,
    exact hy',
    rw comm_p x' y',
    exact hz,
   end,
   plus_ident := 
   begin
    intro x,
    have t : (x ⨁ Ideal_zero R).I = {z : R.R | ∃ (x' y' : R.R), x' ∈ x.I ∧ y' ∈ (Ideal_zero R).I
                                                             ∧ z = (x' + y')},
    exact rfl,
    have t' : {z : R.R | ∃ (x' y' : R.R), x' ∈ x.I ∧ y' ∈ (Ideal_zero R).I ∧ z = (x' + y')} = x.I,
    apply funext,
    intro r,
    apply propext,
    split,
    intro H,
    cases H with x' H,
    cases H with y' H,
    cases H with Hx' H,
    cases H with Hy' H,
    have t'' : y' = zero,
    apply s,
    exact Hy',
    rw t'' at H,
    rw ← newt_p_1 x' at H,
    rw H,
    exact Hx',
    intro Hr,
    existsi r,
    existsi zero,
    split,
    exact Hr,
    split,
    exact rfl,
    rw ← newt_p_1 r,
    have t'' : (x ⨁ Ideal_zero R).I = x.I,
    rw t,
    exact t',
    apply ideal_equality_condition,
    exact t'',
   end,
   mult_assoc := 
   begin
    intros w y z,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hx,
    specialize hx (set_num (set_mult w (y ⨂ z)) (nonempty_set_mult w (y ⨂ z)))
                  (set_mult_mult_set w (y ⨂ z)),
    have hx' := hx,
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    rw eqx,
    apply fin_sum_member_condition ((w ⨂ y) ⨂ z) fx nx,
    intro n,
    specialize hx n,
    intro I,
    intro hI,
    cases hx with x' hx,
    cases hx with H hx,
    cases H with y' H,
    cases H with hy' H,
    cases H with y'' H,
    cases H with hy'' H,
    specialize hy'' (set_num (set_mult y z) (nonempty_set_mult y z))
                    (set_mult_mult_set y z),
    cases hx with p hx,
    cases hx with q hx,
    rw hx,
    apply (multiplication_conditions I).2,
    apply (multiplication_conditions I).1,
    cases hy'' with ny'' hy'',
    cases hy'' with fy'' hy'',
    cases hy'' with eqy'' hy'',
    rw eqy'' at H,
    rw mul_proof y' fy'' ny'' at H,
    rw H,
    apply fin_sum_member_condition I (mul_fun y' fy'') ny'',
    intro nrxr,
    specialize hy'' nrxr,
    cases hy'' with xy'' hy'',
    cases hy'' with Hy'' hy'',
    cases hy'' with yy'' hy'',
    cases hy'' with zy'' hy'',
    have t : mul_fun y' fy'' nrxr = y' * (fy'' nrxr),
    exact rfl,
    rw t,
    rw hy'',
    cases Hy'' with y₀ Hy'',
    cases Hy'' with Hy₀ Hy'',
    cases Hy'' with y₁ Hy'',
    cases Hy'' with Hy₁ Hy'',
    rw Hy'',
    rw ← assoc_m,
    rw assoc_m y' yy'' (y₀ * y₁ * zy''),
    rw assoc_m (y' * yy'') y₀ (y₁ * zy''),
    specialize hI ((y' * yy'') * y₀) (y₁ * zy''),
    have t' : (y' * yy'') * y₀ ∈ (w ⨂ y).I,
    intros I' hI',
    specialize hI' (y' * yy'') y₀,
    apply hI',
    apply (multiplication_conditions w).1,
    exact hy',
    exact Hy₀,
    specialize hI t',
    apply hI,
    apply (multiplication_conditions z).1,
    exact Hy₁, -- end of part one
    intro hx,
    specialize hx (set_num (set_mult (w ⨂ y) z) (nonempty_set_mult (w ⨂ y) z))
                  (set_mult_mult_set (w ⨂ y) z),
    cases hx with nx hx,
    cases hx with fx hx,
    cases hx with eqx hx,
    rw eqx,
    apply fin_sum_member_condition (w ⨂ y ⨂ z) fx nx,
    intro n,
    specialize hx n,
    intros I hI,
    cases hx with x' hx,
    cases hx with H hx,
    cases H with y' H,
    cases H with hy' H,
    cases H with y'' H,
    cases H with hy'' H,
    specialize hy' (set_num (set_mult w y) (nonempty_set_mult w y))
                   (set_mult_mult_set w y),
    cases hx with p hx,
    cases hx with q hx,
    rw hx,
    apply (multiplication_conditions I).2,
    apply (multiplication_conditions I).1, 
    cases hy' with ny' hy',
    cases hy' with fy' hy',
    cases hy' with eqy' hy',
    rw eqy' at H,
    rw mul_proof' y'' fy' ny' at H,
    rw H,
    apply fin_sum_member_condition I (mul_fun' y'' fy') ny',
    intro nrxr,
    specialize hy' nrxr,
    cases hy' with xy' hy',
    cases hy' with Hy' hy',
    cases hy' with yy' hy',
    cases hy' with zy' hy',
    have t : mul_fun' y'' fy' nrxr = (fy' nrxr) * y'',
    exact rfl,
    rw t,
    rw hy',
    cases Hy' with y₀ Hy',
    cases Hy' with Hy₀ Hy',
    cases Hy' with y₁ Hy',
    cases Hy' with Hy₁ Hy',
    rw Hy',
    rw ← assoc_m y₀ y₁ zy',
    rw assoc_m yy' y₀ (y₁ * zy'),
    rw ← assoc_m,
    specialize hI (yy' * y₀) ((y₁ * zy') * y''),
    apply hI,
    apply (multiplication_conditions w).2,
    exact Hy₀,
    intros I' hI',
    specialize hI' (y₁ * zy') y'',
    apply hI',
    apply (multiplication_conditions y).1,
    exact Hy₁,
    exact hy'',
   end,
   mult_liden := 
   begin
    intro x, 
    apply ideal_equality_condition,
    apply funext,
    intro x',
    apply propext,
    split,
    intro H,
    specialize H x,
    apply H,
    exact self_mult_set' x Ideal_one,
    intros H I',
    intro HI',
    specialize HI' one x',
    rw ← newt_m_l x',
    apply HI',
    have t : true,
    cc,
    exact t,
    exact H,
   end,
   mult_riden := 
   begin
    intro I,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hx,
    exact hx I (self_mult_set I Ideal_one),
    intros hx I' hI',
    specialize hI' x one,
    rw ← newt_m_r x,
    apply hI',
    exact hx,
    have t : true,
    cc,
    exact t,
   end,
   lm_distrib := 
   begin
    intros w y z,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hx,
    specialize hx ((w ⨂ y) ⨁ (w ⨂ z)),
    apply hx,
    intros x' y' hx' hy',
    cases hy' with x'' hy',
    cases hy' with y'' hy',
    cases hy' with hx'' hy',
    cases hy' with hy'' hy',
    rw hy',
    rw distribby_l x' x'' y'',
    existsi x' * x'',
    existsi x' * y'',
    split,
    intros I' hI',
    specialize hI' x' x'',
    apply hI',
    exact hx',
    apply hx'',
    split,
    intros I' hI',
    specialize hI' x' y'',
    apply hI',
    exact hx',
    exact hy'',
    exact rfl,
    intro H,
    cases H with x' H,
    cases H with y' H,
    cases H with Hx' H,
    cases H with Hy' H,
    specialize Hx' (w ⨂ y ⨁ z),
    specialize Hy' (w ⨂ y ⨁ z),
    rw H,
    apply (subgroup_under_addition (w ⨂ y ⨁ z)).2.1 x' y',
    apply Hx',
    intros x'' y'' hx'' hy'',
    intros I' hI',
    specialize hI' x'' y'' hx'',
    apply hI',
    existsi y'',
    existsi zero,
    split,
    exact hy'',
    split,
    exact Ideal_has_zero z,
    exact newt_p_1 y'',
    apply Hy',
    intros x'' y'' hx'' hy'' I' hI',
    specialize hI' x'' y'' hx'',
    apply hI',
    existsi zero,
    existsi y'',
    split,
    exact Ideal_has_zero y,
    split,
    exact hy'',
    rw comm_p zero y'',
    exact newt_p_1 y'', 
   end,
   rm_distrib := 
   begin
    intros w y z,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hx,
    specialize hx ((w ⨂ z) ⨁ (y ⨂ z)),
    apply hx,
    intros x' y' hx' hy',
    cases hx' with wx' hx',
    cases hx' with yx' hx',
    cases hx' with hwx' hx',
    cases hx' with hyx' hx',
    rw hx',
    rw distribby_r wx' yx' y',
    existsi wx' * y',
    existsi yx' * y',
    split,
    intros I hI,
    exact hI wx' y' hwx' hy',
    split,
    intros I hI,
    exact hI yx' y' hyx' hy', 
    exact rfl,
    intro hx,
    cases hx with x' hx,
    cases hx with y' hx,
    cases hx with hx' hx,
    cases hx with hy' hx,
    specialize hx' ((w ⨁ y) ⨂ z),
    specialize hy' ((w ⨁ y) ⨂ z),
    rw hx,
    apply (subgroup_under_addition ((w ⨁ y) ⨂ z)).2.1 x' y',
    apply hx',
    intros x'' y'' hx'' hy'',
    intros I hI,
    specialize hI x'' y'',
    apply hI,
    existsi x'',
    existsi zero,
    split,
    exact hx'',
    split,
    exact Ideal_has_zero y,
    exact newt_p_1 x'',
    exact hy'',
    apply hy',
    intros x'' y'' hx'' hy'' I hI,
    specialize hI x'' y'',
    apply hI,
    existsi zero,
    existsi x'',
    split,
    exact Ideal_has_zero w,
    split,
    exact hx'',
    rw comm_p,
    exact newt_p_1 x'',
    exact hy'',
   end,
   zero_lanni := 
   begin
    intro I,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hx,
    exact hx (Ideal_zero R) (self_mult_set (Ideal_zero R) I),
    intro hx,
    have t : x = zero,
    exact hx,
    rw t,
    exact Ideal_has_zero (Ideal_zero R ⨂ I),
   end,
   zero_ranni := 
   begin
    intro I,
    apply ideal_equality_condition,
    funext,
    apply propext,
    split,
    intro hx,
    exact hx (Ideal_zero R) (self_mult_set' (Ideal_zero R) I),
    intro hx,
    have t : x = zero,
    exact hx,
    rw t,
    exact Ideal_has_zero (I ⨂ Ideal_zero R),
   end
  }

lemma idempotent_ideals {R : Ring} (I : Ideal R) : I ⨁ I = I :=
begin
 apply ideal_equality_condition,
 funext,
 apply propext,
 split,
 intro hz,
 cases hz with zx hz,
 cases hz with zy hz,
 cases hz with hzx hz,
 cases hz with hzy hz,
 rw hz,
 exact (subgroup_under_addition I).2.1 zx zy hzx hzy,
 intro hz,
 existsi z,
 existsi zero,
 split,
 exact hz,
 split,
 exact Ideal_has_zero I,
 rw ← newt_p_1 z,
end
