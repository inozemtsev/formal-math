module

public import Green64.Library.Weights.UnfilteredForestListedRows
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Weights / Part030

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredForestFiniteWitness -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Actual conditional representative weight, including its fibre guard.
It is defined at every Output, without assuming Output itself is finite. -/
def sourceOriginalForestOrbitWeight434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (X : Output) (x : State) : ℂ :=
  if physicalFockProjection SP sm BP bm (J+ell) cap x=X then
    (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)/
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X:ℂ)
  else 0

theorem source_original_forest_ORBIT_FLAT434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (f : State → ℂ) (X : Output) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X =
    ∑ x : State,sourceOriginalForestOrbitWeight434 SP sm BP bm J ell cap Vs mu X x*f x := by
  unfold fullPhysicalOrbitAverage
  rw [Finset.sum_div,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases he : physicalFockProjection SP sm BP bm (J+ell) cap x=X
  · simp only [sourceOriginalForestOrbitWeight434,if_pos he]
    ring
  · simp [sourceOriginalForestOrbitWeight434,he]

/-- Finite original G witness index, independent of the queried orbit.
Both ordered endpoints and every repeated-atom witness remain present. -/
abbrev SourceOriginalForestGIndex434 :=
  Σ x : State,State × FullGhostWitness SP sm BP bm (J+ell) cap x

/-- Finite original E witness index, including a freshly sampled ordered
input representative at this visit. -/
abbrev SourceOriginalForestEIndex434 :=
  Σ x : State,FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x

def sourceOriginalForestGFlatCoefficient434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (X : Output)
    (z : SourceOriginalForestGIndex434 SP sm BP bm J ell cap) : ℂ :=
  sourceOriginalForestOrbitWeight434 SP sm BP bm J ell cap Vs mu X z.1 *
    (if (physicalGhostFreshBirths SP sm BP bm (J+ell) cap z.1 z.2.2).Nodup then
      physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu z.1 z.2.1 z.2.2 else 0)

def sourceOriginalForestEFlatCoefficient434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (X : Output)
    (z : SourceOriginalForestEIndex434 SP sm BP bm J ell m cap patterns) : ℂ :=
  sourceOriginalForestOrbitWeight434 SP sm BP bm J ell cap Vs mu X z.1 *
    (if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns z.1 o k z.2 ∧
        (orientedEFreshBirths SP sm BP bm J ell m cap patterns z.2).Nodup then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k z.1 z.2 else 0)

/-- Exact finite-index expansion, valid also on zero-mass fibres. -/
theorem source_original_forest_LISTED_G_FLAT434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List ℕ)
    (F : Output → List ℕ → ℂ) (X : Output) :
    sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N i Vs V mu H F X =
    ∑ z : SourceOriginalForestGIndex434 SP sm BP bm J ell cap,
      sourceOriginalForestGFlatCoefficient434 SP sm BP bm J ell cap q rho N i Vs V mu X z *
        F (physicalFockProjection SP sm BP bm (J+ell) cap z.2.1)
          (H++physicalGhostFreshBirths SP sm BP bm (J+ell) cap z.1 z.2.2) := by
  unfold sourceOriginalForestListedG434
  rw [source_original_forest_ORBIT_FLAT434]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only [sourceOriginalForestGFlatCoefficient434]
  by_cases hb : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup
  · simp only [if_pos hb];ring
  · simp only [if_neg hb,mul_zero,zero_mul]

/-- Exact finite-index E expansion. The full joint K is never factored. -/
theorem source_original_forest_LISTED_E_FLAT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List ℕ)
    (F : Output → List ℕ → ℂ) (X : Output) :
    sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H F X =
    ∑ z : SourceOriginalForestEIndex434 SP sm BP bm J ell m cap patterns,
      sourceOriginalForestEFlatCoefficient434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k X z *
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns z.1 o k z.2)
          (H++orientedEFreshBirths SP sm BP bm J ell m cap patterns z.2) := by
  unfold sourceOriginalForestListedE434
  rw [source_original_forest_ORBIT_FLAT434]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  unfold sourceOrientedPhysicalChoices
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only [sourceOriginalForestEFlatCoefficient434]
  by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z
  · by_cases hb : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup
    · simp only [if_pos hl,if_pos hb,if_pos (And.intro hl hb)];ring
    · simp [hl,hb]
  · simp [hl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootFiniteBind -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {S H O : Type} [Fintype O]

/-- Finite-row iteration. Neither the state nor the register is assumed finite.
The next representative is selected by the next coefficient, never inherited. -/
def sourceOriginalRootBind434
    (a : ℕ → S → H → O → ℂ)
    (out : ℕ → S → H → O → S) (upd : ℕ → S → H → O → H)
    (terminal : S → H → ℂ) : ℕ → ℕ → S → H → ℂ
  | 0, _, x, h => terminal x h
  | n+1, i, x, h => ∑ z : O, a i x h z *
      sourceOriginalRootBind434 a out upd terminal n (i+1)
        (out i x h z) (upd i x h z)

/-- Nested finite sum over all chronological witness strings of the given length. -/
def sourceOriginalRootPathSum434 (n : ℕ) (f : List O → ℂ) : ℂ :=
  match n with
  | 0 => f []
  | n+1 => ∑ z : O, sourceOriginalRootPathSum434 n (fun zs => f (z::zs))

def sourceOriginalRootPathValue434
    (a : ℕ → S → H → O → ℂ)
    (out : ℕ → S → H → O → S) (upd : ℕ → S → H → O → H)
    (terminal : S → H → ℂ) : List O → ℕ → S → H → ℂ
  | [], _, x, h => terminal x h
  | z::zs, i, x, h => a i x h z *
      sourceOriginalRootPathValue434 a out upd terminal zs (i+1)
        (out i x h z) (upd i x h z)

theorem source_original_root_PATH_SUM_MUL434
    (n : ℕ) (c : ℂ) (f : List O → ℂ) :
    sourceOriginalRootPathSum434 n (fun zs => c*f zs) =
      c*sourceOriginalRootPathSum434 n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [sourceOriginalRootPathSum434, ih, Finset.mul_sum]

theorem source_original_root_BIND_PATH_EXACT434
    (a : ℕ → S → H → O → ℂ)
    (out : ℕ → S → H → O → S) (upd : ℕ → S → H → O → H)
    (terminal : S → H → ℂ) (n i : ℕ) (x : S) (h : H) :
    sourceOriginalRootBind434 a out upd terminal n i x h =
    sourceOriginalRootPathSum434 n
      (fun zs => sourceOriginalRootPathValue434 a out upd terminal zs i x h) := by
  induction n generalizing i x h with
  | zero => rfl
  | succ n ih =>
      simp only [sourceOriginalRootBind434, sourceOriginalRootPathSum434,
        sourceOriginalRootPathValue434, source_original_root_PATH_SUM_MUL434]
      apply Finset.sum_congr rfl
      intro z hz
      rw [ih]

def sourceOriginalRootRowBudget434 (B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n+1, i => B i * sourceOriginalRootRowBudget434 B n (i+1)

theorem source_original_root_ROW_BUDGET_NONNEG434
    (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i) (n i : ℕ) :
    0 ≤ sourceOriginalRootRowBudget434 B n i := by
  induction n generalizing i with
  | zero => simp [sourceOriginalRootRowBudget434]
  | succ n ih => exact mul_nonneg (hB i) (ih (i+1))

/-- Register-uniform backward induction. Repetitions and inactive sentinels
are allowed in H; the update may depend on every current draw. No conditional
law or independence of the future register is an assumption. -/
theorem source_original_root_UNIFORM_SUFFIX434
    (a : ℕ → S → H → O → ℂ)
    (out : ℕ → S → H → O → S) (upd : ℕ → S → H → O → H)
    (terminal : S → H → ℂ) (W : S → ℝ) (B : ℕ → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hterminal : ∀ x h, ‖terminal x h‖ ≤ W x)
    (hrow : ∀ i x h, (∑ z : O, ‖a i x h z‖ * W (out i x h z)) ≤ B i * W x)
    (n i : ℕ) (x : S) (h : H) :
    ‖sourceOriginalRootBind434 a out upd terminal n i x h‖ ≤
      sourceOriginalRootRowBudget434 B n i * W x := by
  induction n generalizing i x h with
  | zero => simpa [sourceOriginalRootBind434, sourceOriginalRootRowBudget434] using hterminal x h
  | succ n ih =>
      have hb := source_original_root_ROW_BUDGET_NONNEG434 B hB n (i+1)
      calc
        ‖sourceOriginalRootBind434 a out upd terminal (n+1) i x h‖ ≤
            ∑ z : O, ‖a i x h z *
              sourceOriginalRootBind434 a out upd terminal n (i+1)
                (out i x h z) (upd i x h z)‖ := norm_sum_le _ _
        _ ≤ ∑ z : O, ‖a i x h z‖ *
              (sourceOriginalRootRowBudget434 B n (i+1) * W (out i x h z)) := by
          apply Finset.sum_le_sum
          intro z hz
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (ih (i+1) _ _) (norm_nonneg _)
        _ = sourceOriginalRootRowBudget434 B n (i+1) *
              (∑ z : O, ‖a i x h z‖ * W (out i x h z)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          ring
        _ ≤ sourceOriginalRootRowBudget434 B n (i+1) * (B i * W x) :=
          mul_le_mul_of_nonneg_left (hrow i x h) hb
        _ = sourceOriginalRootRowBudget434 B (n+1) i * W x := by
          simp only [sourceOriginalRootRowBudget434]
          ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootRademacher -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalRootSign434 (b : Bool) : ℂ := if b then -1 else 1

theorem source_original_root_SIGN_NORM434 (b : Bool) :
    ‖sourceOriginalRootSign434 b‖ = 1 := by
  cases b <;> norm_num [sourceOriginalRootSign434]

theorem source_original_root_SIGN_SQUARE434 (b : Bool) :
    sourceOriginalRootSign434 b * sourceOriginalRootSign434 b = 1 := by
  cases b <;> norm_num [sourceOriginalRootSign434]

variable {A : Type} [Fintype A] [DecidableEq A]

def sourceOriginalRootSignFlip434 (x : A) (e : A → Bool) (a : A) : Bool :=
  if a=x then !(e a) else e a

def sourceOriginalRootSignFlipEquiv434 (x : A) : (A → Bool) ≃ (A → Bool) where
  toFun := sourceOriginalRootSignFlip434 x
  invFun := sourceOriginalRootSignFlip434 x
  left_inv := by
    intro e
    funext a
    by_cases h : a=x <;> simp [sourceOriginalRootSignFlip434,h]
  right_inv := by
    intro e
    funext a
    by_cases h : a=x <;> simp [sourceOriginalRootSignFlip434,h]

theorem source_original_root_DISTINCT_SIGN_SUM434
    (x y : A) (hxy : x ≠ y) :
    (∑ e : A → Bool, sourceOriginalRootSign434 (e x) *
      sourceOriginalRootSign434 (e y)) = 0 := by
  let f : (A → Bool) → ℂ := fun e =>
    sourceOriginalRootSign434 (e x) * sourceOriginalRootSign434 (e y)
  have hf (e : A → Bool) : f (sourceOriginalRootSignFlipEquiv434 x e) = -f e := by
    dsimp [f,sourceOriginalRootSignFlipEquiv434,sourceOriginalRootSignFlip434]
    simp only [ite_true, if_neg (Ne.symm hxy)]
    cases hx : e x <;> cases hy : e y <;> norm_num [sourceOriginalRootSign434]
  have hh := (sourceOriginalRootSignFlipEquiv434 x).sum_comp f
  have hs : (∑ e : A → Bool, f e) = -(∑ e : A → Bool, f e) := by
    calc
      _ = ∑ e : A → Bool, f (sourceOriginalRootSignFlipEquiv434 x e) := hh.symm
      _ = ∑ e : A → Bool, -f e := Finset.sum_congr rfl (fun e _ => hf e)
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hz : (2:ℂ)*(∑ e : A → Bool,f e)=0 := by
    calc
      _ = (∑ e : A → Bool,f e)+(∑ e : A → Bool,f e) := by ring
      _ = 0 := by conv_lhs => lhs; rw [hs]
                  ring
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Exact finite normalized equality identity. An independent copy of this
field is required at each selected child/edge. -/
theorem source_original_root_RADEMACHER_EQUALITY434 (x y : A) :
    (∑ e : A → Bool,sourceOriginalRootSign434 (e x)*sourceOriginalRootSign434 (e y)) /
      (Fintype.card (A → Bool):ℂ) = if x=y then 1 else 0 := by
  by_cases h : x=y
  · subst y
    simp only [source_original_root_SIGN_SQUARE434, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, if_pos rfl]
    exact div_self (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (A → Bool) ≠ 0))
  · rw [if_neg h, source_original_root_DISTINCT_SIGN_SUM434 x y h, zero_div]

/-- Pointwise centering identity; the random scalar must remain inside
the expectation. No probabilistic independence is used in this algebra. -/
theorem source_original_root_SENTINEL_CENTERING434
    (e : A → Bool) (x y sx sy : A) :
    sourceOriginalRootSign434 (e x)*sourceOriginalRootSign434 (e y) =
    (sourceOriginalRootSign434 (e sx)*sourceOriginalRootSign434 (e sy)) *
      ((sourceOriginalRootSign434 (e x)*sourceOriginalRootSign434 (e sx)) *
       (sourceOriginalRootSign434 (e y)*sourceOriginalRootSign434 (e sy))) := by
  calc
    _ = (sourceOriginalRootSign434 (e x)*sourceOriginalRootSign434 (e y)) *
      ((sourceOriginalRootSign434 (e sx)*sourceOriginalRootSign434 (e sx)) *
       (sourceOriginalRootSign434 (e sy)*sourceOriginalRootSign434 (e sy))) := by
        rw [source_original_root_SIGN_SQUARE434,source_original_root_SIGN_SQUARE434]
        ring
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootIndependentSigns -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact tensorization of normalized finite averages. This is one
independent sample for each index, with no cardinality loss. -/
theorem source_original_root_INDEPENDENT_AVERAGE434
    {E B : Type} [Fintype E] [Fintype B] [Nonempty B]
    (f : E → B → ℂ) :
    (∑ h : E → B,∏ e : E,f e (h e)) / (Fintype.card (E → B):ℂ) =
      ∏ e : E,((∑ b : B,f e b)/(Fintype.card B:ℂ)) := by
  have hs := Fintype.prod_sum f
  rw [←hs, Finset.prod_div_distrib]
  congr 1
  simp [Fintype.card_fun]

/-- Each selected child has its own independent sign field. This remains
valid for repeated endpoint values and for edges sharing vertices. -/
theorem source_original_root_INDEPENDENT_EDGE_EQUALITIES434
    {E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
    (left right : E → A) :
    (∑ h : E → (A → Bool),∏ e : E,
      sourceOriginalRootSign434 (h e (left e)) *
        sourceOriginalRootSign434 (h e (right e))) /
      (Fintype.card (E → (A → Bool)):ℂ) =
    ∏ e : E,(if left e=right e then (1:ℂ) else 0) := by
  rw [source_original_root_INDEPENDENT_AVERAGE434 (fun (e : E) (b : A → Bool) =>
    sourceOriginalRootSign434 (b (left e))*sourceOriginalRootSign434 (b (right e)))]
  apply Finset.prod_congr rfl
  intro e he
  exact source_original_root_RADEMACHER_EQUALITY434 (left e) (right e)

/-- Centering all independent edge endpoints retains the product of the
random sentinel signs INSIDE the finite average. -/
theorem source_original_root_INDEPENDENT_CENTERED_EQUALITIES434
    {E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
    (left right sentinelLeft sentinelRight : E → A) :
    (∑ h : E → (A → Bool),
      (∏ e : E,sourceOriginalRootSign434 (h e (sentinelLeft e)) *
        sourceOriginalRootSign434 (h e (sentinelRight e))) *
      (∏ e : E,
        (sourceOriginalRootSign434 (h e (left e)) *
          sourceOriginalRootSign434 (h e (sentinelLeft e))) *
        (sourceOriginalRootSign434 (h e (right e)) *
          sourceOriginalRootSign434 (h e (sentinelRight e))))) /
      (Fintype.card (E → (A → Bool)):ℂ) =
    ∏ e : E,(if left e=right e then (1:ℂ) else 0) := by
  rw [←source_original_root_INDEPENDENT_EDGE_EQUALITIES434 left right]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  exact (source_original_root_SENTINEL_CENTERING434 (h e)
    (left e) (right e) (sentinelLeft e) (sentinelRight e)).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootRegisterFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {S H O : Type} [Fintype O]

/-- Unregistered chronological rows, still resampling each representative. -/
def sourceOriginalRootPlainBind434 (a : ℕ → S → O → ℂ)
    (out : ℕ → S → O → S) (F : S → ℂ) : ℕ → ℕ → S → ℂ
  | 0, _, x => F x
  | n+1, i, x => ∑ z : O, a i x z *
      sourceOriginalRootPlainBind434 a out F n (i+1) (out i x z)

/-- Exact extraction of a multiplicative register observable, using its
one-write identity only. In applications P is the phase product on already
written blocks. All phases remain inside their actual row sums. -/
theorem source_original_root_REGISTER_PHASE_FACTOR434
    (a : ℕ → S → O → ℂ) (out : ℕ → S → O → S)
    (upd : ℕ → S → H → O → H)
    (P : ℕ → H → ℂ) (phase : ℕ → S → O → ℂ)
    (hwrite : ∀ i x h z, P (i+1) (upd i x h z) = P i h * phase i x z)
    (F : S → ℂ) (n i : ℕ) (x : S) (h : H) :
    sourceOriginalRootBind434 (fun i x _ z => a i x z)
      (fun i x _ z => out i x z) upd (fun y h' => P (i+n) h' * F y) n i x h =
    P i h * sourceOriginalRootPlainBind434
      (fun i x z => a i x z * phase i x z) out F n i x := by
  induction n generalizing i x h with
  | zero => simp [sourceOriginalRootBind434, sourceOriginalRootPlainBind434]
  | succ n ih =>
      have hi : i+(n+1) = (i+1)+n := by omega
      simp only [sourceOriginalRootBind434, sourceOriginalRootPlainBind434, hi]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [ih, hwrite]
      ring

/-- Exact transfer of terminal equalities to their child rows. Here C i h
is the product of constraints whose children have already been written.
Zero factors, repeated values, and inactive values need no division. -/
theorem source_original_root_REGISTER_CONSTRAINT_FACTOR434
    (a : ℕ → S → H → O → ℂ)
    (out : ℕ → S → H → O → S) (upd : ℕ → S → H → O → H)
    (C : ℕ → H → ℂ) (test : ℕ → S → H → O → ℂ)
    (hwrite : ∀ i x h z, C (i+1) (upd i x h z) = C i h * test i x h z)
    (F : S → ℂ) (n i : ℕ) (x : S) (h : H) :
    sourceOriginalRootBind434 a out upd
      (fun y h' => C (i+n) h' * F y) n i x h =
    C i h * sourceOriginalRootBind434
      (fun i x h z => a i x h z * test i x h z)
      out upd (fun y _ => F y) n i x h := by
  induction n generalizing i x h with
  | zero => simp [sourceOriginalRootBind434]
  | succ n ih =>
      have hi : i+(n+1) = (i+1)+n := by omega
      simp only [sourceOriginalRootBind434, hi]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [ih, hwrite]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootDistinctness -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sourceOriginalRootPrefixDistinct434 {A : Type} (n : ℕ) (x : ℕ → A) : Prop :=
  ∀ i < n,∀ j < n,x i=x j → i=j

def sourceOriginalRootDistinctFactor434 {A : Type} (x : ℕ → A) (i : ℕ) : ℂ :=
  1-∑ j ∈ Finset.range i,if x i=x j then 1 else 0

/-- Distinctness as a chronological product. The proof handles the first
repeat by a unique predecessor, rather than requiring every factor to be
an indicator or nonnegative. -/
theorem source_original_root_DISTINCT_PRODUCT434
    {A : Type} (n : ℕ) (x : ℕ → A) :
    (if sourceOriginalRootPrefixDistinct434 n x then (1:ℂ) else 0) =
      ∏ i ∈ Finset.range n,sourceOriginalRootDistinctFactor434 x i := by
  induction n with
  | zero => simp [sourceOriginalRootPrefixDistinct434]
  | succ n ih =>
    rw [Finset.prod_range_succ,←ih]
    by_cases hd : sourceOriginalRootPrefixDistinct434 n x
    · by_cases hn : ∀ j < n,x n ≠ x j
      · have hs : sourceOriginalRootPrefixDistinct434 (n+1) x := by
          intro i hi j hj hij
          by_cases hin : i=n
          · subst i
            by_cases hjn : j=n
            · exact hjn.symm
            · exact False.elim (hn j (by omega) hij)
          · by_cases hjn : j=n
            · subst j
              exact False.elim (hn i (by omega) hij.symm)
            · exact hd i (by omega) j (by omega) hij
        have hz : (∑ j ∈ Finset.range n,if x n=x j then (1:ℂ) else 0)=0 := by
          apply Finset.sum_eq_zero
          intro j hj
          exact if_neg (hn j (Finset.mem_range.mp hj))
        simp [hs,hd,sourceOriginalRootDistinctFactor434,hz]
      · push_neg at hn
        obtain ⟨j,hj,hxj⟩ := hn
        have hs : ¬sourceOriginalRootPrefixDistinct434 (n+1) x := by
          intro hh
          have he := hh n (by omega) j (by omega) hxj
          omega
        have hone : (∑ k ∈ Finset.range n,if x n=x k then (1:ℂ) else 0)=1 := by
          rw [Finset.sum_eq_single j]
          · simp [hxj]
          · intro k hk hkj
            apply if_neg
            intro hxk
            exact hkj (hd k (Finset.mem_range.mp hk) j hj (hxk.symm.trans hxj))
          · intro hnj
            exact False.elim (hnj (Finset.mem_range.mpr hj))
        simp [hs,hd,sourceOriginalRootDistinctFactor434,hone]
    · have hs : ¬sourceOriginalRootPrefixDistinct434 (n+1) x := by
        intro hh
        apply hd
        intro i hi j hj hij
        exact hh i (by omega) j (by omega) hij
      simp [hs,hd]

/-- The algebraic prefix predicate is exactly numerical LIST Nodup. -/
theorem source_original_root_PREFIX_LIST_NODUP434
    {A : Type} (n : ℕ) (x : ℕ → A) :
    sourceOriginalRootPrefixDistinct434 n x ↔
      (List.ofFn (fun i : Fin n => x i.val)).Nodup := by
  rw [List.nodup_ofFn]
  constructor
  · intro h i j hij
    exact Fin.ext (h i.val i.isLt j.val j.isLt hij)
  · intro h i hi j hj hij
    exact congrArg Fin.val (h (a₁:=⟨i,hi⟩) (a₂:=⟨j,hj⟩) hij)

/-- Option-valued private-sentinel padding is injective precisely when
no two performed slots carry the same numeric value. -/
theorem source_original_root_PADDED_INJECTIVE434
    {Addr Num : Type} (v : Addr → Option Num) :
    Function.Injective (fun a : Addr => (v a).elim (Sum.inr a) Sum.inl : Addr → Num ⊕ Addr) ↔
    (∀ a b p,v a=some p → v b=some p → a=b) := by
  constructor
  · intro h a b p ha hb
    apply h
    simp [ha,hb]
  · intro h a b hab
    cases ha : v a with
    | none =>
      cases hb : v b with
      | none => simpa [ha,hb] using hab
      | some q => simp [ha,hb] at hab
    | some p =>
      cases hb : v b with
      | none => simp [ha,hb] at hab
      | some q =>
        have hpq : p=q := by simpa [ha,hb] using hab
        exact h a b p ha (hpq ▸ hb)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestExpansion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- One optional strictly earlier parent at every potential address. -/
abbrev SourceOriginalRootForest434 (n : ℕ) :=
  (i : Fin n) → Option (Fin i.val)

def sourceOriginalRootForestRank434 {n : ℕ} (p : SourceOriginalRootForest434 n) : ℕ :=
  ∑ i : Fin n,(p i).elim 0 (fun _ => 1)

def sourceOriginalRootForestEquality434 {A : Type} {n : ℕ}
    (p : SourceOriginalRootForest434 n) (x : ℕ → A) : ℂ :=
  ∏ i : Fin n,(p i).elim 1 (fun j => if x i.val=x j.val then 1 else 0)

def sourceOriginalRootForestTerm434 {A : Type} {n : ℕ}
    (p : SourceOriginalRootForest434 n) (x : ℕ → A) : ℂ :=
  ∏ i : Fin n,(p i).elim 1 (fun j => -(if x i.val=x j.val then 1 else 0))

theorem source_original_root_FOREST_TERM_SIGN434
    {A : Type} {n : ℕ} (p : SourceOriginalRootForest434 n) (x : ℕ → A) :
    sourceOriginalRootForestTerm434 p x =
      (-1:ℂ)^(sourceOriginalRootForestRank434 p)*sourceOriginalRootForestEquality434 p x := by
  unfold sourceOriginalRootForestTerm434 sourceOriginalRootForestRank434
    sourceOriginalRootForestEquality434
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases h : p i <;> simp [h] <;> split_ifs <;> norm_num

/-- Exact signed increasing-forest expansion of numerical distinctness.
No local injectivity hypothesis is imposed on the label array. -/
theorem source_original_root_FOREST_EXPANSION434
    {A : Type} (n : ℕ) (x : ℕ → A) :
    (if sourceOriginalRootPrefixDistinct434 n x then (1:ℂ) else 0) =
      ∑ p : SourceOriginalRootForest434 n,
        (-1:ℂ)^(sourceOriginalRootForestRank434 p)*sourceOriginalRootForestEquality434 p x := by
  simp_rw [←source_original_root_FOREST_TERM_SIGN434]
  unfold sourceOriginalRootForestTerm434
  rw [←Fintype.prod_sum (fun (i : Fin n) (a : Option (Fin i.val)) =>
    a.elim (1:ℂ) (fun j => -(if x i.val=x j.val then 1 else 0)))]
  rw [source_original_root_DISTINCT_PRODUCT434]
  rw [←Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fintype.sum_option]
  dsimp only [Option.elim]
  rw [Finset.sum_neg_distrib,Fin.sum_univ_eq_sum_range
    (fun j => if x i.val=x j then (1:ℂ) else 0) i.val]
  unfold sourceOriginalRootDistinctFactor434
  ring

/-- Rank is literally the number of selected children. -/
theorem source_original_root_FOREST_RANK_CARD434
    {n : ℕ} (p : SourceOriginalRootForest434 n) :
    sourceOriginalRootForestRank434 p =
      ((Finset.univ : Finset (Fin n)).filter (fun i => (p i).isSome)).card := by
  unfold sourceOriginalRootForestRank434
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : p i <;> simp [h]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootCount -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {A : Type} [Fintype A] [DecidableEq A]

def sourceOriginalGlobalRootParentGraph434 (p : A → Option A) : Finset (A × A) :=
  Finset.univ.filter (fun z => p z.1=some z.2)

def sourceOriginalGlobalRootParentRank434 (p : A → Option A) : ℕ :=
  ∑ a : A,(p a).elim 0 (fun _ => 1)

theorem source_original_global_root_PARENT_GRAPH_CARD434 (p : A → Option A) :
    (sourceOriginalGlobalRootParentGraph434 p).card=sourceOriginalGlobalRootParentRank434 p := by
  unfold sourceOriginalGlobalRootParentGraph434 sourceOriginalGlobalRootParentRank434
  rw [Finset.card_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  cases h : p a <;> simp [h]

theorem source_original_global_root_PARENT_GRAPH_INJECTIVE434 :
    Function.Injective (sourceOriginalGlobalRootParentGraph434 (A:=A)) := by
  intro p q hpq
  have hh (a b : A) : p a=some b ↔ q a=some b := by
    have ht := congrArg (fun s : Finset (A × A) => (a,b)∈s) hpq
    simpa [sourceOriginalGlobalRootParentGraph434] using ht
  funext a
  cases hp : p a with
  | none =>
    cases hq : q a with
    | none => rfl
    | some b => exact False.elim (by simpa [hp] using (hh a b).mpr hq)
  | some b => exact ((hh a b).mp hp).symm

theorem source_original_global_root_PARENT_RANK_COUNT434 (r : ℕ) :
    Fintype.card {p : A → Option A // sourceOriginalGlobalRootParentRank434 p=r} ≤
      (Fintype.card A)^(2*r) := by
  let C := (Finset.univ : Finset (A × A)).powersetCard r
  let e : {p : A → Option A // sourceOriginalGlobalRootParentRank434 p=r} →
      {s : Finset (A × A) // s∈C} := fun p =>
    ⟨sourceOriginalGlobalRootParentGraph434 p.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,(source_original_global_root_PARENT_GRAPH_CARD434 p.val).trans p.property⟩⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    exact source_original_global_root_PARENT_GRAPH_INJECTIVE434 (congrArg Subtype.val h)
  calc
    _ ≤ Fintype.card {s : Finset (A × A) // s∈C} := Fintype.card_le_of_injective e he
    _ = ((Fintype.card A)*(Fintype.card A)).choose r := by
      rw [Fintype.card_coe,Finset.card_powersetCard]
      simp
    _ ≤ ((Fintype.card A)*(Fintype.card A))^r := Nat.choose_le_pow _ _
    _ = _ := by rw [←pow_two,←pow_mul]

def sourceOriginalGlobalRootForestParent434 {n : ℕ}
    (p : SourceOriginalRootForest434 n) (i : Fin n) : Option (Fin n) :=
  (p i).map (fun j => ⟨j.val,lt_trans j.isLt i.isLt⟩)

theorem source_original_global_root_FOREST_PARENT_INJECTIVE434 {n : ℕ} :
    Function.Injective (sourceOriginalGlobalRootForestParent434 (n:=n)) := by
  intro p q hpq
  funext i
  have hh := congrFun hpq i
  dsimp only [sourceOriginalGlobalRootForestParent434] at hh
  cases hp : p i <;> cases hq : q i <;> simp [hp,hq] at hh ⊢
  exact Fin.ext hh

theorem source_original_global_root_FOREST_PARENT_RANK434 {n : ℕ}
    (p : SourceOriginalRootForest434 n) :
    sourceOriginalGlobalRootParentRank434 (sourceOriginalGlobalRootForestParent434 p) =
      sourceOriginalRootForestRank434 p := by
  unfold sourceOriginalGlobalRootParentRank434 sourceOriginalRootForestRank434
  apply Finset.sum_congr rfl
  intro i hi
  cases h : p i <;> simp [sourceOriginalGlobalRootForestParent434,h]

/-- Rank-r increasing forests cost at most A^(2r), with A the number of
POTENTIAL addresses; no injectivity of their numeric readout is assumed. -/
theorem source_original_global_root_FOREST_RANK_COUNT434 (n r : ℕ) :
    Fintype.card {p : SourceOriginalRootForest434 n // sourceOriginalRootForestRank434 p=r} ≤
      n^(2*r) := by
  let e : {p : SourceOriginalRootForest434 n // sourceOriginalRootForestRank434 p=r} →
      {p : Fin n → Option (Fin n) // sourceOriginalGlobalRootParentRank434 p=r} :=
    fun p => ⟨sourceOriginalGlobalRootForestParent434 p.val,
      (source_original_global_root_FOREST_PARENT_RANK434 p.val).trans p.property⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    exact source_original_global_root_FOREST_PARENT_INJECTIVE434 (congrArg Subtype.val h)
  exact (Fintype.card_le_of_injective e he).trans
    (by simpa using source_original_global_root_PARENT_RANK_COUNT434 (A:=Fin n) r)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootRankSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Rank counts selected children, hence never exceeds the potential length. -/
theorem source_original_global_root_RANK_LE434
    {A : ℕ} (p : SourceOriginalRootForest434 A) :
    sourceOriginalRootForestRank434 p ≤ A := by
  unfold sourceOriginalRootForestRank434
  calc
    _ ≤ ∑ _i : Fin A,(1:ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      cases h : p i <;> simp [h]
    _ = A := by simp

/-- Finite rank aggregation; no infinite series and no additional forest law. -/
theorem source_original_global_root_FOREST_NORM_SUM434
    (A : ℕ) (F : SourceOriginalRootForest434 A → ℂ)
    (B : ℕ → ℝ) (hB : ∀ r,0 ≤ B r)
    (hF : ∀ p,‖F p‖ ≤ B (sourceOriginalRootForestRank434 p)) :
    ‖∑ p,F p‖ ≤ ∑ r ∈ Finset.range (A+1),(A:ℝ)^(2*r)*B r := by
  have hm : ∀ p ∈ (Finset.univ : Finset (SourceOriginalRootForest434 A)),
      sourceOriginalRootForestRank434 p ∈ Finset.range (A+1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (source_original_global_root_RANK_LE434 p))
  calc
    _ ≤ ∑ p,‖F p‖ := norm_sum_le _ _
    _ = ∑ r ∈ Finset.range (A+1),
        ∑ p ∈ Finset.univ.filter (fun p => sourceOriginalRootForestRank434 p=r),‖F p‖ :=
      (Finset.sum_fiberwise_of_maps_to hm (fun p => ‖F p‖)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      let s := Finset.univ.filter (fun p : SourceOriginalRootForest434 A =>
        sourceOriginalRootForestRank434 p=r)
      have hc : s.card ≤ A^(2*r) := by
        have he : Fintype.card {p : SourceOriginalRootForest434 A //
            sourceOriginalRootForestRank434 p=r}=s.card :=
          Fintype.card_of_subtype s (fun p => by simp [s])
        rw [←he]
        exact source_original_global_root_FOREST_RANK_COUNT434 A r
      have hcR : (s.card:ℝ) ≤ (A:ℝ)^(2*r) := by exact_mod_cast hc
      calc
        _ ≤ ∑ _p ∈ s,B r := by
          apply Finset.sum_le_sum
          intro p hp
          have he := (Finset.mem_filter.mp hp).2
          simpa only [he] using hF p
        _ = (s.card:ℝ)*B r := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcR (hB r)

/-- With two per-forest banks, retain the smaller one at every rank. -/
theorem source_original_global_root_FOREST_TWO_BANKS434
    (A : ℕ) (F : SourceOriginalRootForest434 A → ℂ)
    (P lo b a delta : ℝ) (hP : 0 ≤ P) (hlo : 0 ≤ lo)
    (hb : 0 ≤ b) (ha : 0 ≤ a) (hd : 0 ≤ delta) (N : ℕ)
    (hLow : ∀ p,‖F p‖ ≤ P*lo^N*b^(2*sourceOriginalRootForestRank434 p))
    (hHigh : ∀ p,‖F p‖ ≤ P*a^N*delta^(sourceOriginalRootForestRank434 p)) :
    ‖∑ p,F p‖ ≤ ∑ r ∈ Finset.range (A+1),
      (A:ℝ)^(2*r)*min (P*lo^N*b^(2*r)) (P*a^N*delta^r) := by
  apply source_original_global_root_FOREST_NORM_SUM434
  · intro r
    exact le_min (by positivity) (by positivity)
  · intro p
    exact le_min (hLow p) (hHigh p)
end Green64Analytic.CorrelationSquare

end

end

