import rings_and_properties
import natural_number_lemmas

local infixr ` + ` : 80 := plus
local infixr ` * ` : 80 := mult

/-- These definitions and results will be used when i come to prove that Ideal multiplication is
    associative. -/

/- A finite sum of elements of a Ring -/
def fin_sum {R : Ring} (f : ℕ → R.R) : ℕ → R.R
 | 0 := f 0
 | (nat.succ n) := f (nat.succ n) + fin_sum n

/- (material for) The sum of two such finite sums -/
def fin_sum_sum {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) : ℕ → R.R
 | 0 := fx 0
 | (nat.succ n) := if n < nx then (fx (nat.succ n) + fin_sum fx n)
                   else (fy (nat.succ n - nat.succ nx) + fin_sum_sum n)

/- The three definitions below allow us to show that finite sums can form ideals -/

def add_fun {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) : ℕ → R.R
 | 0 := fx 0
 | (nat.succ n) := if n < nx then fx (nat.succ n)
                   else fy (nat.succ n - nat.succ nx)

def mul_fun {R : Ring} (m : R.R) (f : ℕ → R.R) : ℕ → R.R :=
 λ n, m * (f n)

def mul_fun' {R : Ring} (m : R.R) (f : ℕ → R.R) : ℕ → R.R :=
 λ n, (f n) * m

namespace add_fin_sum

/- adding the first nx terms of such a sum of finite sums just produces the first such sum -/
lemma early_sum {R : Ring} (fx fy : ℕ → R.R) : ∀ n : ℕ, fin_sum_sum n fx fy n = fin_sum fx n :=
begin
 intro n,
 induction n with n hn,
 { exact rfl, },
 { have h : n < nat.succ n,
   { exact nat.lt_succ_self n, },
   have h' : fin_sum_sum (nat.succ n) fx fy (nat.succ n) 
           = ite (n < nat.succ n) (fx (nat.succ n) + fin_sum fx n) -- 'ite' means 'if..then..else'
                 (fy (nat.succ n - nat.succ (nat.succ n)) + fin_sum_sum (nat.succ n) fx fy n),
   { exact rfl, },
   -- it's not very elegant, but this produces the equality desired by way of the defintion.
   -- This three-step method (prove the inequality, get to the ite by rfl and then use simp)
   -- will be used over and over again in later lemmas.
   have h'' : fin_sum_sum (nat.succ n) fx fy (nat.succ n) = fx (nat.succ n) + fin_sum fx n,
   { simp [h, h'], },
   exact h'', },
end

/- similar to the above -/
lemma early_sum' {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) :
∀ n : ℕ, n < nx → fin_sum_sum nx fx fy n = fin_sum fx n :=
begin
 intros n hn,
 induction n with n indh,
 { exact rfl, },
 { have h : n < nx,
   { apply nat.lt_of_succ_lt,
     exact hn, },
   specialize indh h,
   have h' : fin_sum_sum nx fx fy (nat.succ n) 
             = ite (n < nx) (fx (nat.succ n) + fin_sum fx n)
                   (fy (nat.succ n - nat.succ nx) + fin_sum_sum nx fx fy n),
   { exact rfl, },
   have h'' : fin_sum_sum nx fx fy (nat.succ n) = fx (nat.succ n) + fin_sum fx n,
   { simp [h, h'], },
   calc
    fin_sum_sum nx fx fy (nat.succ n) = fx (nat.succ n) + fin_sum fx n : by exact h''
                                  ... = fin_sum fx (nat.succ n)        : by exact rfl, },
end

/- Showing that, given the right argument, the material for the sum of finite sums returns the
   value we want it to return.  -/
lemma sum_is_sum {R : Ring} (nx ny : ℕ) (fx fy : ℕ → R.R) :
(fin_sum_sum nx fx fy) (nat.succ (nat.add nx ny)) = (fin_sum fx nx) + (fin_sum fy ny) :=
begin
 induction ny with ny indhy,
 { have h : nat.add nx 0 = nx,
   { exact nat.add_zero nx, },
   rw h,
   have h' : fin_sum_sum nx fx fy (nat.succ nx) 
           = ite (nx < nx) (fx (nat.succ nx) + fin_sum fx nx) 
                           (fy (nat.succ nx - nat.succ nx) + fin_sum_sum nx fx fy nx),
   { exact rfl, },
   have h'' : ¬ nx < nx,
   { exact lt_irrfl nx },
   -- see, here is the three step method again!
   have h''' : fin_sum_sum nx fx fy (nat.succ nx)
             = fy (nat.succ nx - nat.succ nx) + fin_sum_sum nx fx fy nx,
   { simp [h', h''], },
   rw h''',
   have h'''' : nat.succ nx - nat.succ nx = 0,
   { exact nat.sub_self (nat.succ nx), },
   rw h'''',
   calc
    fy 0 + fin_sum_sum nx fx fy nx = fin_sum_sum nx fx fy nx  + fy 0 : by rw plus_comm
                               ... = fin_sum fx nx + fy 0            : by rw early_sum
                               ... = fin_sum fx nx + fin_sum fy 0    : by exact rfl, },
 { rw add_succ_commute nx ny,
   have h := succ_add_nlt nx ny,
   have h' : fin_sum_sum nx fx fy (nat.succ (nat.succ (nat.add nx ny)))
             = ite (nat.succ (nat.add nx ny) < nx)
               (fx (nat.succ (nat.succ (nat.add nx ny))) + fin_sum fx (nat.succ (nat.add nx ny)))
               (fy (nat.succ (nat.succ (nat.add nx ny)) - nat.succ nx)
               + fin_sum_sum nx fx fy (nat.succ (nat.add nx ny))),
   { exact rfl, },
   calc
    fin_sum_sum nx fx fy (nat.succ (nat.succ (nat.add nx ny)))
        = fy (nat.succ (nat.succ (nat.add nx ny)) - nat.succ nx)
          + fin_sum_sum nx fx fy (nat.succ (nat.add nx ny))      : by simp [h, h'] -- three step!
    ... = fy (nat.succ (nat.succ (nat.add nx ny)) - nat.succ nx) + fin_sum fx nx + fin_sum fy ny 
                                                                 : by rw indhy
    ... = fy (nat.succ ny) + fin_sum fx nx + fin_sum fy ny       : by{ simp,
                                                                       rw succ_add_minus_is_succ }
    ... = fy (nat.succ ny) + fin_sum fy ny + fin_sum fx nx       : by rw plus_comm 
                                                                      (fin_sum fx nx)
                                                                      (fin_sum fy ny)
    ... = (fy (nat.succ ny) + fin_sum fy ny) + fin_sum fx nx     : by rw plus_assoc
    ... = fin_sum fy (nat.succ ny) + fin_sum fx nx               : by exact rfl
    ... = fin_sum fx nx + fin_sum fy (nat.succ ny)               : by rw plus_comm, },
end

/- This is the key result in this section: that, for any two finite sums, their sum can be given 
   as another finite sum -/
lemma add_fin_sum {R : Ring} (nx : ℕ) (fx fy : ℕ → R.R) :
∀ n : ℕ, fin_sum (add_fun nx fx fy) n = fin_sum_sum nx fx fy n := 
begin
 intro n,
 induction n with n indh,
 { exact rfl, },
 { have hn : n < nx ∨ ¬ n < nx,
   { exact lt_decidable nx n, },
   cases hn,
   { have h : fin_sum (add_fun nx fx fy) (nat.succ n)
              = add_fun nx fx fy (nat.succ n) + fin_sum (add_fun nx fx fy) n,
     { exact rfl, },
     have h' : add_fun nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n))
                                                   (fy (nat.succ n - nat.succ nx)),
     { exact rfl, },
     have h'' : add_fun nx fx fy (nat.succ n) = fx (nat.succ n),
     { simp [hn, h'] },
     have h''' : nat.succ n = nx ∨ nat.succ n < nx,
     { exact nat.eq_or_lt_of_le (nat.succ_le_of_lt hn), },
     calc
      fin_sum (add_fun nx fx fy) (nat.succ n)
          = add_fun nx fx fy (nat.succ n) + fin_sum (add_fun nx fx fy) n : by exact h
      ... = fx (nat.succ n) + fin_sum_sum nx fx fy n : by { rw h'', rw indh }
      ... = fx (nat.succ n) + fin_sum fx n           : by rw early_sum' nx fx fy n hn
      ... = fin_sum fx (nat.succ n)                  : by exact rfl 
      ... = fin_sum_sum nx fx fy (nat.succ n)        : by { symmetry,
                                                            cases h''',
                                                            { rw h''',
                                                              exact early_sum fx fy nx, },
                                                            { exact early_sum' 
                                                              nx fx fy (nat.succ n) h''' }, }, },
   -- it may not be entirely clear what's going on in the last line of the calc above, and that's 
   -- my bad, but essentially all i'm doing is considering the two possible cases, where 
   -- nat.succ n = nx and where nat.succ n < nx, and using the different forms of early_sum to 
   -- prove the equality in each one of these cases in turn 

   { have h : fin_sum (add_fun nx fx fy) (nat.succ n)
              = add_fun nx fx fy (nat.succ n) + fin_sum (add_fun nx fx fy) n,
     { exact rfl, },
     have h' : fin_sum_sum nx fx fy (nat.succ n) 
              = ite (n < nx) (fx (nat.succ n) + fin_sum fx n)
                (fy (nat.succ n - nat.succ nx) + fin_sum_sum nx fx fy n),
     { exact rfl, },
     have h'' : fin_sum_sum nx fx fy (nat.succ n) 
              = fy (nat.succ n -  nat.succ nx) + fin_sum_sum nx fx fy n,
     { simp [hn, h'], },
     have h''' : add_fun nx fx fy (nat.succ n) = ite (n < nx) (fx (nat.succ n))
                                                 (fy (nat.succ n - nat.succ nx)),
     { exact rfl, },
     have h'''' : add_fun nx fx fy (nat.succ n) = fy (nat.succ n - nat.succ nx),
     { simp [hn, h'''], },
     calc
      fin_sum (add_fun nx fx fy) (nat.succ n)
          = add_fun nx fx fy (nat.succ n) + fin_sum (add_fun nx fx fy) n : by exact h
      ... = fy (nat.succ n - nat.succ nx) + fin_sum (add_fun nx fx fy) n : by rw h''''
      ... = fy (nat.succ n - nat.succ nx) + fin_sum_sum nx fx fy n       : by rw indh
      ... = fin_sum_sum nx fx fy (nat.succ n)                            : by rw ← h'', }, },
end

end add_fin_sum

namespace mul_fin_sum

/- left multiples of finite sums are finite sums  -/
lemma mul_fin_sum {R : Ring} (y : R.R) (f : ℕ → R.R) :
∀ n : ℕ, y * (fin_sum f n) = fin_sum (mul_fun y f) n :=
begin
 intro n,
 induction n with n hn,
 { exact rfl, },
 { have h : fin_sum (mul_fun y f) (nat.succ n) 
            = mul_fun y f (nat.succ n) + fin_sum (mul_fun y f) n,
   { exact rfl, },
   have h' : mul_fun y f (nat.succ n) = y * f (nat.succ n),
   { exact rfl, },
   symmetry,
   calc
    fin_sum (mul_fun y f) (nat.succ n) 
        = mul_fun y f (nat.succ n) + fin_sum (mul_fun y f) n : by exact h
    ... = (y * f (nat.succ n)) + y * fin_sum f n : by { rw h', rw ← hn } 
    ... = y * (f (nat.succ n) + fin_sum f n)     : by rw ← left_distributivity
    ... = y * fin_sum f (nat.succ n)             : by exact rfl, },
end

/- right multiples of finite sums are finite sums  -/
lemma mul_fin_sum' {R : Ring} (y : R.R) (f : ℕ → R.R) :
∀ n : ℕ, (fin_sum f n) * y = fin_sum (mul_fun' y f) n :=
begin
 intro n,
 induction n with n hn,
 { exact rfl, },
 { have h : fin_sum (mul_fun' y f) (nat.succ n)
           = mul_fun' y f (nat.succ n) + fin_sum (mul_fun' y f) n,
   { exact rfl, },
   have h' : mul_fun' y f (nat.succ n) = (f (nat.succ n)) * y,
   { exact rfl, },
   symmetry,
   calc
    fin_sum (mul_fun' y f) (nat.succ n)
        = mul_fun' y f (nat.succ n) + fin_sum (mul_fun' y f) n : by exact h
    ... = ((f (nat.succ n)) * y) + (fin_sum f n) * y : by { rw h', rw ← hn }
    ... = (f (nat.succ n) + fin_sum f n) * y         : by rw ← right_distributivity
    ... = (fin_sum f (nat.succ n)) * y : by exact rfl, },  
end

end mul_fin_sum
