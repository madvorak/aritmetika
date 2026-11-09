import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Have

structure RobinsonovaAritmetika (U : Type) [Zero U] (S : U → U) [Add U] [Mul U] [LE U] where
  nula_neni_naslednik : ∀ x : U, S x ≠ 0
  ostatni_jsou_naslednici : ∀ x : U, x ≠ 0 → ∃ y : U, x = S y
  nesrazi_se : ∀ x y : U, S x = S y → x = y
  zavedeni_nerovnosti : ∀ x y : U, x ≤ y ↔ ∃ z : U, x + z = y
  pricteni_nuly : ∀ x : U, x + 0 = x
  pricteni_naslednika : ∀ x y : U, x + S y = S (x + y)
  nasobeni_nuly : ∀ x : U, x * 0 = 0
  nasobeni_naslednika : ∀ x y : U, x * S y = x * y + x

structure PeanovaAritmetika (U : Type) [Zero U] (S : U → U) [Add U] [Mul U] [LE U] extends RobinsonovaAritmetika U S where
  schema_indukce (φ : U → Prop) : φ 0 ∧ (∀ x : U, φ x → φ (S x)) → ∀ x : U, φ x -- Pozor, není first-order !!!!!!

example : PeanovaAritmetika ℕ Nat.succ where
  nula_neni_naslednik := by grind
  ostatni_jsou_naslednici := (by cases · <;> grind)
  nesrazi_se := by grind
  zavedeni_nerovnosti := by
    intro m n
    constructor
    · intro hmn
      use n - m
      omega
    · intro ⟨k, hk⟩
      exact Nat.le.intro hk
  pricteni_nuly := by grind
  pricteni_naslednika := by grind
  nasobeni_nuly := by grind
  nasobeni_naslednika := by grind
  schema_indukce (φ : ℕ → Prop) := by
    intro ⟨h0, hS⟩ x
    induction x with
    | zero => exact h0
    | succ n ih => exact hS n ih

-- Přirozená čísla se dvěma nestandardními prvky
def Na2 : Type := ℕ ⊕ Fin 2

def Na2.nula : Na2 := Sum.inl 0
instance : Zero Na2 := ⟨Na2.nula⟩

def Na2.nasl : Na2 → Na2
| Sum.inl n => Sum.inl n.succ
| Sum.inr x => Sum.inr (x + 1)

def Na2.plus : Na2 → Na2 → Na2
| Sum.inl n, Sum.inl m => Sum.inl (n + m)
| Sum.inr x, Sum.inr y => Sum.inr (x + y)
| Sum.inr x, Sum.inl n => Sum.inr (Fin.ofNat 2 (n + x.val))
| Sum.inl n, Sum.inr x => Sum.inr (Fin.ofNat 2 (n + x.val))
instance : Add Na2 := ⟨Na2.plus⟩

def Na2.krat : Na2 → Na2 → Na2
| Sum.inl n, Sum.inl m => Sum.inl (m * n)
| Sum.inr x, Sum.inr y => Sum.inr (x * y)
| Sum.inl 0, Sum.inr _ => Sum.inl 0
| Sum.inr _, Sum.inl 0 => Sum.inl 0
| Sum.inl n, Sum.inr x => Sum.inr (Fin.ofNat 2 (n * x.val))
| Sum.inr x, Sum.inl n => Sum.inr (Fin.ofNat 2 (n * x.val))
instance : Mul Na2 := ⟨Na2.krat⟩

instance : LE Na2 := ⟨(∃ z : Na2, · + z = ·)⟩

example : RobinsonovaAritmetika Na2 Na2.nasl where
  nula_neni_naslednik := by
    intro a
    cases a with
    | inl n =>
      show Sum.inl n.succ ≠ Sum.inl 0
      simp
    | inr x =>
      show Sum.inr (x + 1) ≠ Sum.inl 0
      simp
  ostatni_jsou_naslednici := by
    intro a ha
    cases a with
    | inl n =>
      cases n with
      | zero =>
        exfalso
        exact false_of_ne ha
      | succ n =>
        use Sum.inl n
        rfl
    | inr x =>
      if hx0 : x = 0 then
        use Sum.inr 1
        exact hx0 ▸ rfl
      else
        have hx1 : x = 1
        · omega
        use Sum.inr 0
        exact hx1 ▸ rfl
  nesrazi_se := by
    intro a b hab
    cases a <;> cases b <;> grind [Na2.nasl]
  zavedeni_nerovnosti := by
    intros
    rfl
  pricteni_nuly := by
    intro a
    cases a with
    | inl n =>
      show Na2.plus (Sum.inl n) (Sum.inl 0) = Sum.inl n
      simp [Na2.plus]
      rfl
    | inr x =>
      show Na2.plus (Sum.inr x) (Sum.inl 0) = Sum.inr x
      simp [Na2.plus]
      rfl
  pricteni_naslednika := by
    intro a b
    show Na2.plus a b.nasl = (a + b).nasl
    cases a with
    | inl n =>
      cases b with
      | inl m =>
        rfl
      | inr y =>
        show Sum.inr _ = Sum.inr _
        simp
        grind
    | inr x =>
      cases b with
      | inl m =>
        show Sum.inr _ = Sum.inr _
        simp only [Fin.isValue, Sum.inr.injEq, Fin.ofNat_add]
        grind
      | inr y =>
        show Sum.inr _ = Sum.inr _
        simp
        grind
  nasobeni_nuly := by
    intro a
    cases a with
    | inl n =>
      show Sum.inl _ = Sum.inl _
      simp
    | inr x =>
      show Sum.inl _ = Sum.inl _
      simp
  nasobeni_naslednika := by
    intro a b
    cases a with
    | inl n =>
      cases b with
      | inl m =>
        show Sum.inl _ = Sum.inl _
        simp
        ring
      | inr y =>
        cases n with
        | zero =>
          rfl
        | succ =>
          show Sum.inr _ = Sum.inr _
          if hy0 : y = 0 then
            simp [hy0]
          else
            have hy1 : y = 1
            · omega
            simp [hy1]
            grind
    | inr x =>
      cases b with
      | inl m =>
        cases m with
        | zero =>
          show Sum.inr _ = Sum.inr _
          simp
        | succ n =>
          show Sum.inr _ = Sum.inr _
          if hx0 : x = 0 then
            simp [hx0]
          else
            have hx1 : x = 1
            · omega
            simp [hx1]
            grind
      | inr y =>
        show Sum.inr _ = Sum.inr _
        grind

example : ¬ PeanovaAritmetika Na2 Na2.nasl := by
  -- Pro first-order PA by důkaz šel stejně.
  intro ⟨_, schema⟩
  have nasl_nasl_neq : ∀ x : Na2, x.nasl.nasl ≠ x
  · apply schema
    constructor
    · show Sum.inl 2 ≠ Sum.inl 0
      simp
    · intro x hx
      cases x with
      | inl n =>
        simp [Na2.nasl] at hx ⊢
        grind
      | inr i =>
        exfalso
        simp [Na2.nasl] at hx
        grind
  exact nasl_nasl_neq (Sum.inr 0) rfl

-- Přirozená čísla s nekonečně mnoha nestandardními prvky
def NaN : Type := ℕ ⊕ ℕ

def NaN.nula : NaN := Sum.inl 0
instance : Zero NaN := ⟨NaN.nula⟩

def NaN.nasl : NaN → NaN
| Sum.inl n => Sum.inl n.succ
| Sum.inr m => Sum.inr m

def NaN.plus : NaN → NaN → NaN
| Sum.inl n, Sum.inl m => Sum.inl (n + m)
| Sum.inl _, Sum.inr m => Sum.inr m
| Sum.inr n, _         => Sum.inr n
instance : Add NaN := ⟨NaN.plus⟩

def NaN.krat : NaN → NaN → NaN
| Sum.inl n, Sum.inl m => Sum.inl (m * n)
| Sum.inl _, Sum.inr m => Sum.inr m
| Sum.inr _, Sum.inl 0 => 0
| Sum.inr n, _         => Sum.inr n
instance : Mul NaN := ⟨NaN.krat⟩

instance : LE NaN := ⟨(∃ z : NaN, · + z = ·)⟩

example : RobinsonovaAritmetika NaN NaN.nasl where
  nula_neni_naslednik := by
    intro a
    cases a with
    | inl n =>
      show Sum.inl n.succ ≠ Sum.inl 0
      simp
    | inr x =>
      show Sum.inr x ≠ Sum.inl 0
      simp
  ostatni_jsou_naslednici := by
    intro a ha
    cases a with
    | inl n =>
      cases n with
      | zero =>
        exfalso
        exact false_of_ne ha
      | succ n =>
        use Sum.inl n
        rfl
    | inr x =>
      use Sum.inr x
      rfl
  nesrazi_se := by
    intro a b hab
    cases a <;> cases b <;> grind [NaN.nasl]
  zavedeni_nerovnosti := by
    intros
    rfl
  pricteni_nuly := by
    intro a
    cases a with
    | inl n =>
      show NaN.plus (Sum.inl n) (Sum.inl 0) = Sum.inl n
      simp [NaN.plus]
      rfl
    | inr x =>
      show NaN.plus (Sum.inr x) (Sum.inl 0) = Sum.inr x
      simp [NaN.plus]
      rfl
  pricteni_naslednika := by
    intro a b
    show NaN.plus a b.nasl = (a + b).nasl
    cases a with
    | inl n =>
      cases b with
      | inl m =>
        rfl
      | inr y =>
        rfl
    | inr x =>
      rfl
  nasobeni_nuly := by
    intro a
    cases a with
    | inl n =>
      show Sum.inl _ = Sum.inl _
      simp
    | inr x =>
      rfl
  nasobeni_naslednika := by
    intro a b
    cases a with
    | inl n =>
      cases b with
      | inl m =>
        show Sum.inl _ = Sum.inl _
        simp
        ring
      | inr y =>
        rfl
    | inr x =>
      cases b with
      | inl m =>
        cases m with
        | zero =>
          rfl
        | succ n =>
          rfl
      | inr y =>
        rfl

example : ¬ PeanovaAritmetika NaN NaN.nasl := by
  -- Pro first-order PA by důkaz šel stejně.
  intro ⟨_, schema⟩
  have nasl_neq : ∀ x : NaN, x.nasl ≠ x
  · apply schema
    constructor
    · show Sum.inl 1 ≠ Sum.inl 0
      simp
    · intro x hx
      cases x with
      | inl n =>
        simp [NaN.nasl] at hx ⊢
        grind
      | inr i =>
        exfalso
        simp [NaN.nasl] at hx
        exact false_of_ne hx
  exact nasl_neq (Sum.inr 0) rfl
