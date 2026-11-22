import Lean

/-! Discrete lemmas for the Li–Liu audit. Lean 4.12.0, core library only. -/
namespace LiLiuAudit

/-- Both changes of variable are invertible on the whole integer lattice. -/
theorem shiftCoordinates (a m h t : Int) :
    (m - (m - h) = h ∧ m - (m - a) = a) ∧
    ((t - m) + m = t ∧ (a + m) - m = a) ∧
    (m - (t - m) = 2 * m - t) := by
  omega

/-- The two sieved coordinates have the same parity. -/
theorem parityOfShifts (a m : Int) :
    (a - m) % 2 = (a + m) % 2 := by omega

/-- An odd centre and an odd summation variable give two even coordinates. -/
theorem oddCentre (a m : Int) (ha : a % 2 = 1) (hm : m % 2 = 1) :
    (a - m) % 2 = 0 ∧ (a + m) % 2 = 0 := by omega

private theorem uniqueMultiple {N k : Nat} (hk : 0 < k) (hu : k < 2 * N)
    (hd : N ∣ k) : k = N := by
  obtain ⟨j, rfl⟩ := hd
  cases j with
  | zero => simp at hk
  | succ j =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [Nat.mul_succ] at hu
      omega

/-- On the two supports, equality and opposition modulo N each pick one shift. -/
theorem supportResidues (N m n : Nat) (hm : 10 * m < N)
    (hl : 4 * N < 5 * n) (hr : 5 * n < 6 * N) :
    (N ∣ n - m ↔ n = N + m) ∧ (N ∣ n + m ↔ n = N - m) := by
  have hnm : m < n := by omega
  have hmN : m < N := by omega
  constructor
  · constructor
    · intro h
      have e := uniqueMultiple (N := N) (k := n - m) (by omega) (by omega) h
      omega
    · intro e
      have h : n - m = N := by omega
      rw [h]
      exact Nat.dvd_refl N
  · constructor
    · intro h
      have e := uniqueMultiple (N := N) (k := n + m) (by omega) (by omega) h
      omega
    · intro e
      have h : n + m = N := by omega
      rw [h]
      exact Nat.dvd_refl N

private theorem gcdAdd (x y : Nat) : Nat.gcd x (y + x) = Nat.gcd x y := by
  simpa using Nat.gcd_add_mul_self x y 1

/-- Both partners selected by the support have the same gcd with N as m. -/
theorem unitOnBothShifts (N m : Nat) (h : m ≤ N) :
    Nat.gcd N (N + m) = Nat.gcd m N ∧ Nat.gcd N (N - m) = Nat.gcd m N := by
  constructor
  · rw [Nat.add_comm, gcdAdd, Nat.gcd_comm]
  · let k := N - m
    have e : m + k = N := by dsimp [k]; omega
    have e' : k + m = N := by omega
    change Nat.gcd N k = Nat.gcd m N
    calc
      Nat.gcd N k = Nat.gcd k N := Nat.gcd_comm _ _
      _ = Nat.gcd k m := by rw [← e, gcdAdd]
      _ = Nat.gcd m k := Nat.gcd_comm _ _
      _ = Nat.gcd m N := by rw [← e', gcdAdd]

section Average
variable {ι R : Type} [OfNat R 0] [Add R] [LE R] [DecidableRel (fun x y : R => x ≤ y)]

/-- n copies of the scalar, defined without division or positivity assumptions. -/
def copies (r : R) : Nat → R
  | 0 => 0
  | n+1 => r + copies r n

/-- Sum bound using the actual list of indices above a threshold, valid also
    for signed real weights. Only the elementary ordered-addition laws are inputs. -/
theorem thresholdBudget (f : ι → R) (xs : List ι) (cut cap : R)
    (zeroadd : ∀ x : R, 0 + x = x)
    (assoc : ∀ x y z : R, (x + y) + z = x + (y + z))
    (comm : ∀ x y : R, x + y = y + x)
    (addBound : ∀ {a b c d : R}, a ≤ b → c ≤ d → a + c ≤ b + d)
    (refl : ∀ x : R, x ≤ x)
    (comparable : ∀ x y : R, ¬ x ≤ y → y ≤ x)
    (hcap : ∀ i ∈ xs, f i ≤ cap) :
    xs.foldr (fun i acc => f i + acc) 0 ≤
      copies cut (xs.filter (fun i => !decide (cut ≤ f i))).length +
      copies cap (xs.filter (fun i => decide (cut ≤ f i))).length := by
  induction xs with
  | nil => simpa [copies, zeroadd] using refl 0
  | cons i xs ih =>
    have tail := ih (fun j hj => hcap j (List.mem_cons_of_mem i hj))
    by_cases h : cut ≤ f i
    · have step := addBound (hcap i (by simp)) tail
      simp [h, copies, assoc, List.foldr] at step ⊢
      have swap (a b : R) : cap + (a + b) = a + (cap + b) := by
        rw [← assoc, comm cap a, assoc]
      simpa only [swap] using step
    · have step := addBound (comparable _ _ h) tail
      simpa [h, copies, assoc, List.foldr] using step
end Average

/-- Count loss on deleting a set, with the predicate tested on the original indices. -/
theorem deletionLoss {ι : Type} (xs : List ι) (keep : ι → Bool) :
    (xs.filter keep).length + (xs.filter (fun i => !(keep i))).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    cases h : keep i <;> simp [h] <;> omega

end LiLiuAudit
