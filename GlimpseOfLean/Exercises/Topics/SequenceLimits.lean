import GlimpseOfLean.Library.Basic

namespace Topics

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.

There are many exercises in this file, so do not hesitate to take a
look at the solutions folder if you are stuck, there will be other
exercises.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by linarith

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by linarith

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:
-/

/-- Definition of “u tends to l” -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by
  intro ε hε
  use 0
  intro n hn
  specialize h n
  rw[h]
  simp
  linarith


/-
A small user interface remark: you may have noticed in the previous example that
your editor shows a somewhat ghostly `{u l}` after the `example` word.
This text is not actually present in the Lean file, and cannot be edited.
It is displayed as a hint that Lean inferred we wanted to work with some `u` and `l`.
The fact that `u` should be a sequence and `l` a real numbered was inferred because
the announced conclusion was `seq_limit u l`.

The short version of the above paragraph is you can mostly ignore those ghostly
indications and trust your common sense that `u` is a sequence and `l` a limit.
-/

/-
When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  specialize h (l/2) (by linarith)
  rcases h with ⟨m, hm⟩
  use m
  intro n hn
  specialize hm n hn
  rw[abs_le] at hm
  linarith

/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith


/- Let's do something similar: the squeezing theorem.
In that example it can help to use the `specialize` tactic (introduced in the file
`03Forall.lean`) so that the `linarith` tactic can pick up the relevant files
from the assumptions.
-/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
  intros ε ε_pos
  rcases hu ε ε_pos with ⟨N₁, hN₁⟩
  rcases hw ε ε_pos with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact1 := hN₁ n hn₁
  have fact2 := h n
  have fact3 := h' n
  have fact4 := hN₂ n hn₂

  rw [abs_le] at fact1
  rw [abs_le] at fact4

  have fact5: l - ε ≤ u n := by linarith
  have fact6: w n ≤ l + ε := by linarith
  have fact7: - ε ≤ v n - l := by linarith
  have fact8: v n - l ≤ ε := by linarith
  rw[abs_le]
  tauto


/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma unique_limit : seq_limit u l → seq_limit u l' → l = l' := by
  intro h1
  intro h2
  apply eq_of_abs_sub_le_all
  intro ε hε
  rcases h1 (ε/2) (by linarith) with ⟨n1, hn1⟩
  rcases h2 (ε/2) (by linarith) with ⟨n2, hn2⟩
  let n := max n1 n2
  have temp1: n ≥ n1 := by exact Nat.le_max_left n1 n2
  have temp2: n ≥ n2 := by exact Nat.le_max_right n1 n2
  have temp1 := hn1 n temp1
  have temp2 := hn2 n temp2
  rw[abs_le] at temp1
  rw[abs_le] at temp2
  rw[abs_le]
  have fact1: u n - ε/2 <= l := by linarith
  have fact2: l <= u n + ε/2 := by linarith
  have fact3: u n - ε/2 <= l' := by linarith
  have fact4: l' <= u n + ε/2 := by linarith
  have fact5: - ε <= l - l' := by linarith
  have fact6: l - l' <= ε := by linarith
  tauto


/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by
  intro ε hε
  unfold is_seq_sup at h
  unfold non_decreasing at h'
  have h2 := h.2 ε hε
  rcases h2 with ⟨n0, hn0⟩
  use n0
  intro n hn
  have temp := h' n0 n hn
  have fact1 : - ε <= u n - M := by linarith
  have fact2 := h.1 n
  have fact3 : u n - M <= ε := by linarith
  rw[abs_le]
  tauto


/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.
-/

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

/-
In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction : extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih =>
    have temp := hyp n (n+1) (by linarith)
    apply Nat.succ_le_of_lt
    linarith



/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  intro h
  intro N N'
  let n := max N N'
  use n
  constructor
  · exact Nat.le_max_right N N'
  · have fact1 : n >= N := by exact Nat.le_max_left N N'
    have fact2 := id_le_extraction h n
    linarith



/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.
-/

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  intro h1 ε hε n1
  unfold cluster_point at h1
  rcases h1 with ⟨φ, h2⟩
  rcases h2 with ⟨hφ, hsq⟩
  unfold seq_limit at hsq
  have hsq2 := hsq ε hε
  rcases hsq2 with ⟨n2, hn2⟩
  let n3 := max n1 n2
  have temp := hn2 n3 (by exact Nat.le_max_right n1 n2)
  use φ n3
  constructor
  · have fact1 : n3 >= n1 := by exact Nat.le_max_left n1 n2
    have fact2 := id_le_extraction hφ n3
    linarith
  · exact temp



/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by
  unfold seq_limit
  intro ε hε
  unfold seq_limit at h
  have h1 := h ε hε
  rcases h1 with ⟨n2, hn2⟩
  use n2
  intro n3 hn3
  have h4 := id_le_extraction hφ n3
  exact hn2 (φ n3) (by linarith)


/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  unfold cluster_point at ha
  rcases ha with ⟨φ, h1⟩
  rcases h1 with ⟨hφ, hsq⟩
  have hsq2 := subseq_tendsto_of_tendsto hl hφ
  exact unique_limit hsq hsq2


/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  intro h1
  rcases h1 with ⟨l, hl⟩
  intro ε hε
  rcases hl (ε/2) (by linarith) with ⟨n1, hn1⟩
  use n1
  intro p q
  intro hp
  intro hq
  have fact1 := hn1 p hp
  have fact2 := hn1 q hq
  have fact3:= abs_add (u p - l) (l - u q)
  simp at fact3
  rw[abs_sub_comm l (u q)] at fact3
  linarith


/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  intro ε hε
  unfold CauchySequence at hu
  rcases hu (ε/2) (by linarith) with ⟨ n1, hn1 ⟩
  rcases near_cluster hl (ε/2) (by linarith) n1 with ⟨ n0, hn0 ⟩
  use n0
  intro n hn
  have fact1 := hn1 n0 n hn0.1 (by linarith)
  have fact2:= abs_add (u n0 - l) (u n - u n0)
  simp at fact2
  rw[abs_sub_comm] at fact1
  linarith
