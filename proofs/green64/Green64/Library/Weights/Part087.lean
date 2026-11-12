module

public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part046
public import Green64.Library.Correlation.Part047
public import Green64.Library.Correlation.Part031
public import Green64.Library.Correlation.MemoryOldFockDisintegration
public import Green64.Library.Weights.Part057
public import Green64.Library.Correlation.PhysicalGhostWitnessCollapse
public import Green64.Library.Correlation.Part044

@[expose] public section

/-!
# Weights / Part087

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEdgeOldRatio -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- A one-step exponent change costs only R^t, not R^(a+b) or R^OLD. -/
theorem source_original_edge_POWER_RATIO434
    (V R : ℝ) (hV : 0 < V) (hR : 1 ≤ R)
    (hVR : V ≤ R) (hiR : V⁻¹ ≤ R)
    (n a b t : ℕ) (ha : a ≤ n) (hat : a ≤ t) (hbt : b ≤ t) :
    V^(n-a+b) ≤ R^t*V^n := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  by_cases hab : a ≤ b
  · have he : n-a+b=n+(b-a) := by omega
    have hd : b-a ≤ t := by omega
    rw [he,pow_add]
    have hp : V^(b-a) ≤ R^t :=
      (pow_le_pow_left₀ hV.le hVR _).trans (pow_le_pow_right₀ hR hd)
    exact (mul_le_mul_of_nonneg_left hp (pow_nonneg hV.le n)).trans_eq (mul_comm _ _)
  · have hba : b ≤ a := by omega
    have he : n=(n-a+b)+(a-b) := by omega
    have hd : a-b ≤ t := by omega
    have hp : (V^(a-b))⁻¹ ≤ R^t := by
      rw [←inv_pow]
      exact (pow_le_pow_left₀ (inv_nonneg.mpr hV.le) hiR _).trans
        (pow_le_pow_right₀ hR hd)
    have hp' : 1 ≤ R^t*V^(a-b) := by
      have hh := mul_le_mul_of_nonneg_right hp (pow_nonneg hV.le (a-b))
      simpa only [inv_mul_cancel₀ (ne_of_gt (pow_pos hV (a-b)))] using hh
    calc
      V^(n-a+b) = V^(n-a+b)*1 := by ring
      _ ≤ V^(n-a+b)*(R^t*V^(a-b)) :=
        mul_le_mul_of_nonneg_left hp' (pow_nonneg hV.le _)
      _ = R^t*V^n := by
        conv_rhs => rw [he,pow_add]
        ring

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal per-group OLD evolution, including the injection feasibility
and both original unshared-slot bounds. No numerical distinctness is used. -/
theorem source_original_edge_LEGAL_OLD_COUNTS434
    (st : FullPhysicalState SP sm BP bm (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z)
    (g : BG) :
    let a := ((z.2.2.1.bigChoice g).2).2.1.card
    let b := ((z.2.2.1.bigChoice g).2).1.card
    a ≤ (st.2 g).2.1.val ∧ a ≤ ell+m ∧ b ≤ ell+m ∧
    ((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z).2 g).2.card =
      (st.2 g).2.1.val-a+b := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simpa using Fintype.card_le_of_injective
      ((z.2.2.1.bigChoice g).2).2.2 ((z.2.2.1.bigChoice g).2).2.2.injective
  · exact (Finset.card_le_card (hz.2.2.2.1 g).promotes_unshared).trans
      (memory_source_unshared_count J ell m (patterns z.1) g)
  · exact memory_actual_E_store_count SP sm BP bm J ell m patterns cap st o k z hz g
  · change (physicalPendingOutput (bm g) (J+ell) (cap g) (st.2 g) _ _ _).length = _
    exact pending_output_length _ _ _ _ _ _ _

/-- The actual sector multiplier changes by at most a fixed one-step
factor R^((ell+m)*cardBIG). Full repeated OLD states are retained. -/
theorem source_original_edge_LEGAL_SECTOR_RATIO434
    (V : BG → ℝ) (hV : ∀ g,0 < V g) (R : ℝ) (hR : 1 ≤ R)
    (hVR : ∀ g,V g ≤ R) (hiR : ∀ g,(V g)⁻¹ ≤ R)
    (st : FullPhysicalState SP sm BP bm (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z) :
    sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z) ≤
    R^((ell+m)*Fintype.card BG)*sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V
      (physicalFockProjection SP sm BP bm (J+ell) cap st) := by
  rw [source_original_memory_sector_density_projection434]
  unfold sourceOriginalMemorySectorDensity434
  calc
    _ ≤ ∏ g : BG,R^(ell+m)*(V g)^((st.2 g).2.1.val) := by
      apply Finset.prod_le_prod₀
      · intro g _; exact pow_nonneg (hV g).le _
      · intro g _
        obtain ⟨ha,hat,hbt,he⟩ := source_original_edge_LEGAL_OLD_COUNTS434
          SP sm BP bm J ell m cap patterns st o k z hz g
        rw [he]
        exact source_original_edge_POWER_RATIO434 (V g) R (hV g) hR (hVR g) (hiR g)
          _ _ _ (ell+m) ha hat hbt
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [←pow_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2000000

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

/-- Literal filtered sum of witness norms, with precisely one input physical
mass and no auxiliary sector multiplier. keep may include both OLD gates. -/
def sourceOriginalUnfilteredEdgePlainColumn434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (Y : Output) : ℝ :=
  ∑ st : State,fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu st *
    ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st,
      if (sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧
          sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z=Y) ∧ keep st z
      then ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st z‖ else 0

/-- Transfer the COMPLETE actual column termwise. Only the strictly positive
sector multiplier at Y is cancelled; pi(Y) is never divided out. -/
theorem source_original_edge_FILTERED_COLUMN_TRANSFER434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hV : ∀ g,0<V g) (hmu : ∀ g p,0 < mu g p)
    (Rv : ℝ) (hRv : 1 ≤ Rv) (hVR : ∀ g,V g ≤ Rv) (hiR : ∀ g,(V g)⁻¹ ≤ Rv)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Y : Output) (A : ℝ)
    (hcol : sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap
      patterns keep q rho Vs V mu K zeta theta o k Y ≤
      A*(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y *
        sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V Y)) :
    sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k Y ≤
      A*Rv^((ell+m)*Fintype.card BG)*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y := by
  let D := Rv^((ell+m)*Fintype.card BG)
  let s := sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V
  have hs : 0 < s Y := source_original_memory_sector_density_pos434 SP sm BP bm J ell V hV Y
  have hD : 0 ≤ D := pow_nonneg (le_trans zero_le_one hRv) _
  have ht : s Y*sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k Y ≤
      D*sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k Y := by
    unfold sourceOriginalUnfilteredEdgePlainColumn434 sourceOriginalMemoryOriginalFilteredDensityColumn434
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro st _
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : (sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z=Y) ∧ keep st z
    · rw [if_pos hz]
      have hr := source_original_edge_LEGAL_SECTOR_RATIO434 SP sm BP bm J ell m cap patterns
        V hV Rv hRv hVR hiR st o k z hz.1.1
      rw [hz.1.2] at hr
      have hm := (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu st).le
      have hh := mul_le_mul_of_nonneg_right hr (mul_nonneg hm (norm_nonneg
        (sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k st z)))
      convert hh using 1 <;> dsimp [s,D,sourceOriginalMemoryFullDensityMass434] <;> ring
    · simp only [hz,ite_false,mul_zero,le_refl]
  have hb := mul_le_mul_of_nonneg_left hcol hD
  apply le_of_mul_le_mul_left (a:=s Y) ?_ hs
  calc
    _ ≤ D*sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k Y := ht
    _ ≤ D*(A*(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y*s Y)) := hb
    _ = _ := by dsimp only [D]; ring

/-- Reuse the previously proved complete physical column, for arbitrary
repeated states, and remove its sector density by the literal one-step ratio. -/
theorem source_original_edge_FULL_PLAIN_COLUMN434
    (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0<q) (hq1 : q<1) (hr : 0< rho) (hr1 : rho<1)
    (hVs : ∀ g,0<Vs g) (hV : ∀ g,0<V g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (Rv : ℝ) (hRv : 1 ≤ Rv) (hVR : ∀ g,V g ≤ Rv) (hiR : ∀ g,(V g)⁻¹ ≤ Rv)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu) (Y : Output) :
    sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k Y ≤
    ((∑ nu : Nu,Kcap nu)*(∏ g : SG,memorySmallRowConstant q (Vs g) ell)*
      (∏ g : BG,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
        ((max 1 (V g)⁻¹)^(ell+m)*R^(ell+m))))) *
      Rv^((ell+m)*Fintype.card BG)*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y := by
  apply source_original_edge_FILTERED_COLUMN_TRANSFER434 SP sm BP bm J ell m cap patterns
    (fun _ _ => True) q rho Vs V mu hVs hV hmu Rv hRv hVR hiR K zeta theta o k Y
  have hc := source_original_memory_ORIGINAL_E_density_column434 SP sm BP bm J ell m cap
    patterns q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic
    K zeta theta o k Kcap hK0 hK Y
  simpa only [sourceOriginalMemoryOriginalFilteredDensityColumn434,
    sourceOriginalMemoryOriginalDensityColumn434,and_true] using hc
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgePair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2400000

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

/-- Positive pair mass in the plain physical density, not a transition
probability. Its source mass is present once. -/
def sourceOriginalUnfilteredEdgePlainPair434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (X Y : Output) : ℝ :=
  ∑ st : State,fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu st *
    ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st,
      if (physicalFockProjection SP sm BP bm (J+ell) cap st=X ∧
          sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧
          sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z=Y) ∧ keep st z
      then ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st z‖ else 0

theorem source_original_edge_PAIR_SECTOR434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (X Y : Output) :
    sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V X *
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y =
    sourceOriginalMemoryOriginalFilteredDensityPair434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k X Y := by
  unfold sourceOriginalUnfilteredEdgePlainPair434 sourceOriginalMemoryOriginalFilteredDensityPair434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro st _
  by_cases hx : physicalFockProjection SP sm BP bm (J+ell) cap st=X
  · simp only [sourceOriginalMemoryFullDensityMass434,hx]
    ring
  · simp only [hx,false_and,ite_false,Finset.sum_const_zero,mul_zero]

theorem source_original_edge_PAIR_NONNEG434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (X Y : Output) :
    0 ≤ sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k X Y := by
  apply Finset.sum_nonneg
  intro st _
  apply mul_nonneg (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu st).le
  apply Finset.sum_nonneg
  intro z _
  split_ifs <;> first | exact norm_nonneg _ | exact le_rfl

theorem source_original_edge_PAIR_SOURCE_SUM434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (Y : Output) :
    (∑ X ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y) =
    sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k Y := by
  unfold sourceOriginalUnfilteredEdgePlainPair434 sourceOriginalUnfilteredEdgePlainColumn434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro st _
  rw [←Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  have hm : physicalFockProjection SP sm BP bm (J+ell) cap st ∈
      physicalFockOrbitSupport SP sm BP bm (J+ell) cap :=
    Finset.mem_image.mpr ⟨st,Finset.mem_univ _,rfl⟩
  rw [Finset.sum_eq_single (physicalFockProjection SP sm BP bm (J+ell) cap st)]
  · simp only [eq_self_iff_true,true_and]
  · intro X _ hne
    apply if_neg
    intro h
    exact hne h.1.1.symm
  · exact fun hnot => False.elim (hnot hm)

/-- The row has NO sector-ratio loss. Exact full joint-K reversal is
followed by the existing transposed column bound and cancellation of s(X). -/
theorem source_original_edge_FILTERED_PLAIN_ROW434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu) (X : Output) :
    (∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y) ≤
    ((∑ nu : Nu,Kcap nu)*(∏ g : SG,memorySmallRowConstant q (Vs g) ell)*
      (∏ g : BG,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
        ((max 1 (V g)⁻¹)^(ell+m)*R^(ell+m))))) *
      physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X := by
  have hs := source_original_memory_sector_density_pos434 SP sm BP bm J ell V hV X
  apply le_of_mul_le_mul_left (a:=sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V X) ?_ hs
  rw [Finset.mul_sum]
  simp_rw [source_original_edge_PAIR_SECTOR434]
  have hrow := source_original_memory_FILTERED_pair_row_of_transpose_column434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu hVs hV hmu hr.le K zeta theta o k X
  have hcol := source_original_memory_ORIGINAL_E_density_column434 SP sm BP bm J ell m cap
    patterns q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic
    (fun nu aux s t => K nu aux t s) zeta theta (-o) k Kcap hK0
    (fun nu aux s t => hK nu aux t s) X
  exact (hrow.trans hcol).trans_eq (by ring)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Split a fixed set of OLD indices into two canonically indexed tuples.
Both bag arguments remain joint inside H; repeated atom values are retained. -/
theorem source_original_evolution_ghost_fixed_subset_split434
    (j : ℕ) (A : Finset (Fin j)) (d s : U → ℝ)
    (H : Multiset U → Multiset U → ℝ) :
    (∑ x : Fin j → U,
      (∏ i : ↥A,d (x i.val))*(∏ i : {i : Fin j // i ∉ A},s (x i.val))*
        H (memoryTupleBag (fun i : ↥A => x i.val))
          (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val))) =
    ∑ v : Fin A.card → U,∑ u : Fin (j-A.card) → U,
      (∏ i,d (v i))*(∏ i,s (u i))*H (memoryTupleBag v) (memoryTupleBag u) := by
  classical
  let ea : Fin A.card ≃ ↥A := Fintype.equivOfCardEq (by simp)
  let ec : Fin (j-A.card) ≃ {i : Fin j // i ∉ A} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_coe])
  let e0 := Equiv.piEquivPiSubtypeProd (fun i : Fin j => i ∈ A) (fun _ => U)
  let e : (Fin j → U) ≃ (Fin A.card → U) × (Fin (j-A.card) → U) :=
    e0.trans (Equiv.prodCongr (Equiv.arrowCongr ea.symm (Equiv.refl U))
      (Equiv.arrowCongr ec.symm (Equiv.refl U)))
  rw [←Fintype.sum_prod_type (fun z : (Fin A.card → U) × (Fin (j-A.card) → U) =>
    (∏ i,d (z.1 i))*(∏ i,s (z.2 i))*H (memoryTupleBag z.1) (memoryTupleBag z.2))]
  apply Fintype.sum_equiv e
  intro x
  change (∏ i : ↥A,d (x i.val))*(∏ i : {i : Fin j // i ∉ A},s (x i.val))*
      H (memoryTupleBag (fun i : ↥A => x i.val))
        (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)) =
    (∏ i : Fin A.card,d (x (ea i).val))*
      (∏ i : Fin (j-A.card),s (x (ec i).val))*
      H (memoryTupleBag (fun i : Fin A.card => x (ea i).val))
        (memoryTupleBag (fun i : Fin (j-A.card) => x (ec i).val))
  rw [ea.prod_comp (fun i => d (x i.val)),ec.prod_comp (fun i => s (x i.val))]
  simp only [memoryTupleBag]
  rw [ea.sum_comp (fun i => ({x i.val}:Multiset U)),
    ec.sum_comp (fun i => ({x i.val}:Multiset U))]

/-- Exact binomial disintegration of all indexed deletion subsets, before
the sector factorial. This permits arbitrary different selected/survivor laws. -/
theorem source_original_evolution_ghost_all_subset_split434
    (j : ℕ) (d s : U → ℝ) (H : Multiset U → Multiset U → ℝ) :
    (∑ x : Fin j → U,∑ A : Finset (Fin j),
      (∏ i : ↥A,d (x i.val))*(∏ i : {i : Fin j // i ∉ A},s (x i.val))*
        H (memoryTupleBag (fun i : ↥A => x i.val))
          (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val))) =
    ∑ a ∈ Finset.range (j+1),(j.choose a:ℝ)*
      (∑ v : Fin a → U,∑ u : Fin (j-a) → U,
        (∏ i,d (v i))*(∏ i,s (u i))*H (memoryTupleBag v) (memoryTupleBag u)) := by
  rw [Finset.sum_comm]
  simp_rw [source_original_evolution_ghost_fixed_subset_split434]
  have hp : (Finset.univ : Finset (Fin j)).powerset =
      (Finset.univ : Finset (Finset (Fin j))) := by ext A;simp
  rw [←hp,Finset.sum_powerset_apply_card
    (fun a => ∑ v : Fin a → U,∑ u : Fin (j-a) → U,
      (∏ i,d (v i))*(∏ i,s (u i))*H (memoryTupleBag v) (memoryTupleBag u))]
  simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Source factorial cancellation for unordered indexed deletions. -/
theorem source_original_evolution_ghost_binomial_factorial434
    (j a : ℕ) (ha : a ≤ j) :
    (j.choose a:ℝ)/(j.factorial:ℝ) =
      1/((a.factorial:ℝ)*((j-a).factorial:ℝ)) := by
  have hh := Green64PhysicalEdge.old_injections_over_fock_factorial j a ha
  have hja : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have haa : (a.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hka : ((j-a).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-a)
  push_cast at hh
  field_simp at hh ⊢
  nlinarith only [hh]

/-- True 1/j! Fock disintegration into deleted and surviving tuples. The
1/a! belongs to the deletion-subset sum; no distinct-value quotient occurs. -/
theorem source_original_evolution_ghost_FOCK_subset_disintegration434
    (j : ℕ) (d s : U → ℝ) (H : Multiset U → Multiset U → ℝ) :
    (∑ x : Fin j → U,∑ A : Finset (Fin j),
      ((∏ i : ↥A,d (x i.val))*(∏ i : {i : Fin j // i ∉ A},s (x i.val))*
        H (memoryTupleBag (fun i : ↥A => x i.val))
          (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)))/(j.factorial:ℝ)) =
    ∑ a ∈ Finset.range (j+1),
      (1/((a.factorial:ℝ)*((j-a).factorial:ℝ)))*
      (∑ v : Fin a → U,∑ u : Fin (j-a) → U,
        (∏ i,d (v i))*(∏ i,s (u i))*H (memoryTupleBag v) (memoryTupleBag u)) := by
  simp_rw [←Finset.sum_div]
  rw [source_original_evolution_ghost_all_subset_split434,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  rw [mul_div_right_comm,source_original_evolution_ghost_binomial_factorial434 j a hle]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostParameters -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem source_original_evolution_visit_q_bounds434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N i : ℕ) :
    0 ≤ sourceVisitQ q N i ∧ sourceVisitQ q N i ≤ Real.sqrt q := by
  have hs := Real.sq_sqrt hq
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := (Real.sqrt_le_one).mpr hq1
  have hqs : q ≤ Real.sqrt q := by nlinarith
  unfold sourceVisitQ
  split_ifs
  · exact ⟨hs0,le_rfl⟩
  · exact ⟨hq,hqs⟩

/-- A source zero birth uses counting residue mass, with no reciprocal modulus. -/
theorem source_original_evolution_birth_norm_mass434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) :
    (∑ z : Atom P modulus,‖sourceBirthNu (fun p => (mu p:ℂ)) z‖) = ∑ p,mu p := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp only [sourceBirthNu,birthMass,apply_ite,norm_zero,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (hmu p)]
  change (∑ r : ZMod (modulus p),if r=0 then mu p else 0)=mu p
  rw [Finset.sum_ite_eq']
  simp

theorem source_original_evolution_double_birth_norm434
    {U : Type} [Fintype U] [DecidableEq U]
    (old : List U) (zero : U → Prop) [DecidablePred zero]
    (A : Finset (Fin old.length)) {b : ℕ} (fresh : Fin b → U)
    (alpha chi gamma : ℂ) (nu : U → ℂ) :
    ‖sourceGhostTerm old zero A fresh alpha chi (2*gamma) nu‖ =
      (2:ℝ)^b*‖sourceGhostTerm old zero A fresh alpha chi gamma nu‖ := by
  simp only [sourceGhostTerm,norm_mul,norm_pow,mul_pow]
  norm_num
  ring

/-- The concrete Schur weight requested in the task satisfies both scalar
ghost controls. These are arithmetic consequences, not norm premises. -/
theorem source_original_evolution_weight_controls434
    (q rho W : ℝ) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    0 < w ∧ 1 ≤ w ∧
      1/(rho*w)+Real.sqrt q/rho^2 ≤ 1 ∧
      (2*W/rho)/w+Real.sqrt q/rho^2 ≤ 1 := by
  dsimp only
  let g := Real.sqrt q/rho^2
  let w := max 1 (4*W/(rho*(1-g)))
  have hw : 1 ≤ w := le_max_left _ _
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hd : 0 < rho*(1-g) := mul_pos hr (sub_pos.mpr hg)
  have hb : 4*W ≤ w*(rho*(1-g)) :=
    (div_le_iff₀ hd).mp (le_max_right 1 _)
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hfirst : 1/(rho*w) ≤ 1-g := by
    apply (div_le_iff₀ (mul_pos hr hwp)).mpr
    nlinarith only [hb,hW]
  have hsecond : (2*W/rho)/w ≤ 1-g := by
    rw [div_div]
    apply (div_le_iff₀ (mul_pos hr hwp)).mpr
    nlinarith only [hb,hW0]
  exact ⟨hwp,hw,by linarith only [hfirst],by linarith only [hsecond]⟩

/-- Actual one-group source G, including doubled births, on arbitrary repeated
OLD memory. The bound is uniform in all caps and active slot counts. -/
theorem source_original_evolution_SOURCE_GHOST_doubled_row434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (old : List (Atom P modulus)) (B : ℕ)
    (q rho V W w : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hV : 0 ≤ V) (hVW : V ≤ W) (hW : 1 ≤ W)
    (hw : 0 < w) (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (hmass : ∑ p,mu p ≤ 2) :
    (∑ c : GhostWitnessChoice old (fun z => z.2=0) B,
      (2:ℝ)^c.2.1.val *
        ‖sourceGhostTerm old (fun z => z.2=0) c.1.1 c.2.2
          (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
          (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
          (-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))
          (sourceBirthNu (fun p => (mu p:ℂ)))‖ *
        w^(afterGhost old c.1.1 c.2.2).length) ≤
      Real.exp (4*W*w/rho)*w^old.length := by
  let eta := sourceVisitEta q N i
  let qi := sourceVisitQ q N i
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hqi := source_original_evolution_visit_q_bounds434 q hq hq1 N i
  have hnA : ‖-((eta:ℝ):ℂ)/(rho:ℂ)‖ = eta/rho := by
    simp [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he.1,abs_of_pos hr,eta]
  have hnX : ‖((qi:ℝ):ℂ)/(rho:ℂ)^2‖ = qi/rho^2 := by
    simp [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hqi.1,abs_of_pos hr,qi]
  have hnC : ‖2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))‖ = 2*eta*V/rho := by
    simp [norm_div,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he.1,abs_of_nonneg hV,abs_of_pos hr,eta]
    ring
  have hc : ‖-((eta:ℝ):ℂ)/(rho:ℂ)‖/w +
      ‖((qi:ℝ):ℂ)/(rho:ℂ)^2‖ ≤ 1 := by
    rw [hnA,hnX,div_div]
    have h1 := div_le_div_of_nonneg_right he.2 (mul_pos hr hw).le
    have h2 := div_le_div_of_nonneg_right hqi.2 (sq_nonneg rho)
    exact (add_le_add h1 h2).trans hcontrol
  have hs := source_original_evolution_GHOST_weighted_row434 old
    (fun z => z.2=0) B (-((eta:ℝ):ℂ)/(rho:ℂ))
    (((qi:ℝ):ℂ)/(rho:ℂ)^2)
    (2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ)))
    (sourceBirthNu (fun p => (mu p:ℂ))) w hw hc
  simp_rw [source_original_evolution_double_birth_norm434] at hs
  rw [hnC,source_original_evolution_birth_norm_mass434 modulus mu hmu] at hs
  have hC : 2*eta*V/rho ≤ 2*W/rho := by
    apply div_le_div_of_nonneg_right _ hr.le
    have hh := mul_le_mul_of_nonneg_right he.2 hV
    nlinarith only [hh,hVW]
  have hM : 0 ≤ ∑ p,mu p := Finset.sum_nonneg (fun p _ => hmu p)
  have hecap : (2*eta*V/rho)*w*(∑ p,mu p) ≤ 4*W*w/rho := by
    have hh := mul_le_mul hC hmass hM (by positivity : 0 ≤ 2*W/rho)
    convert mul_le_mul_of_nonneg_left hh hw.le using 1 <;> ring
  exact hs.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hecap) (pow_nonneg hw.le _))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostPhysical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Full original physical G witness row, with every birth weighted by two.
No reachability or distinctness condition is placed on OLD inventory.
The two original finite-state indices and every local witness remain literal. -/
theorem source_original_evolution_PHYSICAL_G_doubled_weighted_row434
    (q rho W w : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (x : FullPhysicalState SP sm BP bm M cap) :
    (∑ y : FullPhysicalState SP sm BP bm M cap,
      ∑ c : FullGhostWitness SP sm BP bm M cap x,
        (2:ℝ)^(∑ g,(c g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
          w^(∑ g,((y.2 g).2).1.val)) ≤
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho) *
        w^(∑ g,((x.2 g).2).1.val) := by
  classical
  let factor (g : BG)
      (c : GhostWitnessChoice (fockToList ((x.2 g).2))
        (fun z : Atom (BP g) (bm g) => z.2=0) (cap g)) : ℝ :=
    (2:ℝ)^c.2.1.val *
      ‖sourceGhostTerm (fockToList ((x.2 g).2)) (fun z => z.2=0) c.1.1 c.2.2
        (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
        (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
        (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
        (sourceBirthNu (fun p => (mu g p:ℂ)))‖ *
      w^(afterGhost (fockToList ((x.2 g).2)) c.1.1 c.2.2).length
  have hf0 (g : BG) (c) : 0 ≤ factor g c := by
    dsimp only [factor]
    positivity
  have hsingle (c : FullGhostWitness SP sm BP bm M cap x) :
      (∑ y : FullPhysicalState SP sm BP bm M cap,
        (2:ℝ)^(∑ g,(c g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
          w^(∑ g,((y.2 g).2).1.val)) ≤ ∏ g,factor g (c g) := by
    by_cases hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c
    · simp_rw [source_original_PHYSICAL_G_witness_target434 SP sm BP bm M cap
        q rho N i V mu x _ c hc]
      simp only [apply_ite,norm_zero,mul_ite,mul_zero,ite_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,if_true]
      dsimp only [sourceOriginalPhysicalGhostWitnessTarget434,sourceOriginalFockFromList434]
      rw [sourceOriginalPhysicalGhostWitnessCoefficient434,norm_prod]
      dsimp only [factor]
      simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
      exact le_rfl
    · simp_rw [source_original_PHYSICAL_G_witness_nofit_zero434 SP sm BP bm M cap
        q rho N i V mu x _ c hc,norm_zero,mul_zero,zero_mul,Finset.sum_const_zero]
      exact Finset.prod_nonneg (fun g _ => hf0 g (c g))
  have hg (g : BG) :
      (∑ c,factor g c) ≤ Real.exp (4*W*w/rho)*w^((x.2 g).2).1.val := by
    simpa only [factor,fockToList_length] using
      source_original_evolution_SOURCE_GHOST_doubled_row434 (bm g)
        (fockToList ((x.2 g).2)) (cap g) q rho (V g) W w N i hq hq1 hr
        (hV g) (hVW g) hW hw hcontrol (mu g) (hmu g) (hmass g)
  have hexp (n : ℕ) :
      Real.exp (4*W*w/rho)^n=Real.exp ((4*W*w/rho)*(n:ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih,←Real.exp_add]
      congr 1
      push_cast
      ring
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ c : FullGhostWitness SP sm BP bm M cap x,∏ g,factor g (c g) :=
      Finset.sum_le_sum (fun c _ => hsingle c)
    _ = ∏ g,∑ c,factor g c := (Fintype.prod_sum factor).symm
    _ ≤ ∏ g,Real.exp (4*W*w/rho)*w^((x.2 g).2).1.val :=
      Finset.prod_le_prod₀
        (fun g _ => Finset.sum_nonneg (fun c _ => hf0 g c)) (fun g _ => hg g)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Finset.prod_pow_eq_pow_sum,hexp]
      congr 2
      ring

/-- Concrete choice of weight, with no extra analytic hypothesis. -/
theorem source_original_evolution_PHYSICAL_G_gamma_row434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (x : FullPhysicalState SP sm BP bm M cap) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    (∑ y : FullPhysicalState SP sm BP bm M cap,
      ∑ c : FullGhostWitness SP sm BP bm M cap x,
        (2:ℝ)^(∑ g,(c g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
          w^(∑ g,((y.2 g).2).1.val)) ≤
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho) *
        w^(∑ g,((x.2 g).2).1.val) := by
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  exact source_original_evolution_PHYSICAL_G_doubled_weighted_row434
    SP sm BP bm M cap q rho W _ N i hq hq1 hr hW hw.1 hw.2.2.1
    V hV hVW mu hmu hmass x
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostOrbit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm M cap
local notation "Output" => FullPhysicalOutput SP sm BP bm M

theorem source_original_evolution_projection_OLD434 (x : State) :
    (∑ g,(((physicalFockProjection SP sm BP bm M cap x).2 g).2).card) =
      ∑ g,((x.2 g).2).1.val := by
  simp [physicalFockProjection,fockMultiset]

/-- Literal local-batch filtered G, erasing only global seen disjointness.
The phase is attached to the original witness, not to an aggregated kernel. -/
def sourceOriginalUnfilteredEvolutionSeenErasedG434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (phase : (x : State) → FullGhostWitness SP sm BP bm M cap x → ℂ)
    (F : Output → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm M cap Vs mu
    (fun x => ∑ y : State,∑ c : FullGhostWitness SP sm BP bm M cap x,
      if (physicalGhostFreshBirths SP sm BP bm M cap x c).Nodup then
        physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c *
          phase x c * F (physicalFockProjection SP sm BP bm M cap y)
      else 0) X

/-- The exact original weighted quotient preserves a pointwise orbit bound.
Its proof uses fullPhysicalMass and physicalOrbitMass on all repeated states. -/
theorem source_original_evolution_ORBIT_pointwise434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (f : State → ℂ) (bound : Output → ℝ)
    (hf : ∀ x,‖f x‖ ≤ bound (physicalFockProjection SP sm BP bm M cap x))
    (X : Output) (hX : X ∈ physicalFockOrbitSupport SP sm BP bm M cap) :
    ‖fullPhysicalOrbitAverage SP sm BP bm M cap Vs mu f X‖ ≤ bound X := by
  have hm := physicalOrbitMass_pos SP sm BP bm M cap Vs mu hVs hmu X hX
  unfold fullPhysicalOrbitAverage
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  calc
    _ ≤ ∑ x ∈ (Finset.univ : Finset State) with
        physicalFockProjection SP sm BP bm M cap x=X,
        ‖(fullPhysicalMass SP sm BP bm M cap Vs mu x:ℂ)*f x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ (Finset.univ : Finset State) with
        physicalFockProjection SP sm BP bm M cap x=X,
        fullPhysicalMass SP sm BP bm M cap Vs mu x*bound X := by
      apply Finset.sum_le_sum
      intro x hx
      have hxX := (Finset.mem_filter.mp hx).2
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (fullPhysicalMass_pos SP sm BP bm M cap Vs mu hVs hmu x)]
      exact mul_le_mul_of_nonneg_left (by simpa [hxX] using hf x)
        (fullPhysicalMass_pos SP sm BP bm M cap Vs mu hVs hmu x).le
    _ = _ := by rw [←Finset.sum_mul];exact mul_comm _ _

/-- Arbitrary original ghost witness phases of norm at most two per birth,
including the true numerical local-batch LIST gate, obey the same row bound. -/
theorem source_original_evolution_SEEN_ERASED_G_weighted_row434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (phase : (x : State) → FullGhostWitness SP sm BP bm M cap x → ℂ)
    (hphase : ∀ x c,‖phase x c‖ ≤ (2:ℝ)^(∑ g,(c g).2.1.val))
    (F : Output → ℂ)
    (hF : ∀ Y ∈ physicalFockOrbitSupport SP sm BP bm M cap,
      ‖F Y‖ ≤ (max 1 (4*W/(rho*(1-Real.sqrt q/rho^2))))^(∑ g,((Y.2 g).2).card))
    (X : Output) (hX : X ∈ physicalFockOrbitSupport SP sm BP bm M cap) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ‖sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm M cap
      q rho N i Vs V mu phase F X‖ ≤
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*w^(∑ g,((X.2 g).2).card) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  apply source_original_evolution_ORBIT_pointwise434 SP sm BP bm M cap Vs mu hVs hmu
    _ (fun Y => Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*w^(∑ g,((Y.2 g).2).card)) _ X hX
  intro x
  have hrw := source_original_evolution_PHYSICAL_G_gamma_row434 SP sm BP bm M cap
    q rho W N i hq hq1 hr hW hg V hV hVW mu (fun g p => (hmu g p).le) hmass x
  rw [source_original_evolution_projection_OLD434]
  calc
    _ ≤ ∑ y : State,∑ c : FullGhostWitness SP sm BP bm M cap x,
        ‖if (physicalGhostFreshBirths SP sm BP bm M cap x c).Nodup then
          physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c *
            phase x c * F (physicalFockProjection SP sm BP bm M cap y) else 0‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun y _ => norm_sum_le _ _))
    _ ≤ ∑ y : State,∑ c : FullGhostWitness SP sm BP bm M cap x,
        (2:ℝ)^(∑ g,(c g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
          w^(∑ g,((y.2 g).2).1.val) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro c _
      split_ifs
      · rw [norm_mul,norm_mul]
        have hFy := hF _ (Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩)
        rw [source_original_evolution_projection_OLD434] at hFy
        have hmul := mul_le_mul (hphase x c) hFy (norm_nonneg _) (by positivity)
        have hmul' := mul_le_mul_of_nonneg_left hmul
          (norm_nonneg (physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c))
        convert hmul' using 1 <;> ring
      · rw [norm_zero];positivity
    _ ≤ _ := hrw

/-- Unfiltered physicalSymmetricVisitGRow itself has the stated weighted
row bound. This statement is not an assertion about its Hilbert norm. -/
theorem source_original_evolution_ORIGINAL_G_weighted_row434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (F : Output → ℂ)
    (hF : ∀ Y ∈ physicalFockOrbitSupport SP sm BP bm M cap,
      ‖F Y‖ ≤ (max 1 (4*W/(rho*(1-Real.sqrt q/rho^2))))^(∑ g,((Y.2 g).2).card))
    (X : Output) (hX : X ∈ physicalFockOrbitSupport SP sm BP bm M cap) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ‖physicalSymmetricVisitGRow SP sm BP bm M cap q rho N i Vs V mu F X‖ ≤
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*w^(∑ g,((X.2 g).2).card) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  unfold physicalSymmetricVisitGRow
  apply source_original_evolution_ORBIT_pointwise434 SP sm BP bm M cap Vs mu hVs hmu
    _ (fun Y => Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*w^(∑ g,((Y.2 g).2).card)) _ X hX
  intro x
  have hrw := source_original_evolution_PHYSICAL_G_gamma_row434 SP sm BP bm M cap
    q rho W N i hq hq1 hr hW hg V hV hVW mu (fun g p => (hmu g p).le) hmass x
  rw [source_original_evolution_projection_OLD434]
  unfold physicalVisitGRow
  simp_rw [←physicalGWitnessKernel_eq_source SP sm BP bm M cap q rho N i V mu,
    physicalGWitnessKernel,Finset.sum_mul]
  calc
    _ ≤ ∑ y : State,∑ c : FullGhostWitness SP sm BP bm M cap x,
        ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c *
          F (physicalFockProjection SP sm BP bm M cap y)‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun y _ => norm_sum_le _ _))
    _ ≤ ∑ y : State,∑ c : FullGhostWitness SP sm BP bm M cap x,
        (2:ℝ)^(∑ g,(c g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
          w^(∑ g,((y.2 g).2).1.val) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul]
      have hFy := hF _ (Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩)
      rw [source_original_evolution_projection_OLD434] at hFy
      have htwo : (1:ℝ) ≤ (2:ℝ)^(∑ g,(c g).2.1.val) := one_le_pow₀ (by norm_num)
      calc
        _ ≤ ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
            w^(∑ g,((y.2 g).2).1.val) :=
          mul_le_mul_of_nonneg_left hFy (norm_nonneg _)
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right htwo
            (mul_nonneg (norm_nonneg (physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c))
              (pow_nonneg hw.1.le (∑ g,((y.2 g).2).1.val)))
          simpa only [one_mul,mul_assoc] using hh
    _ ≤ _ := hrw
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostQuantitative -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The ghost exponent contains only fixed q,rho,W and the group-count bound.
It has no active-slot, residual-depth, OLD-cap, or J dependence. -/
theorem source_original_evolution_GAMMA_polynomial434
    (L W w rho C0 : ℝ) (n : ℕ)
    (hL : 0 < L) (hW : 0 ≤ W) (hw : 0 ≤ w) (hr : 0 < rho)
    (hn : (n:ℝ) ≤ C0*Real.log L) :
    Real.exp (4*W*w*(n:ℝ)/rho) ≤ L^(4*W*w*C0/rho) := by
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 4*W*w/rho)
  convert hh using 1 <;> ring

/-- Original source-depth G witness row in the actual tilted physical law.
All SMALL/BIG types remain independent. The L threshold is even uniform in
the active-slot count and all OLD caps. This is a row theorem, not L2. -/
theorem eventually_source_original_evolution_TILTED_G_row434
    (c q rho W C0 : ℝ) (hc : 0 < c)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hW : 1 ≤ W) (hg : Real.sqrt q/rho^2 < 1) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (M : ℕ) (cap : BG → ℕ) (V : BG → ℝ)
      (hV : ∀ g,0 < V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hBig : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hcount : (Fintype.card BG:ℝ) ≤ C0*Real.log L)
      (i : ℕ) (x : FullPhysicalState SP sm BP bm M cap),
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP bm q N V
    (∑ y : FullPhysicalState SP sm BP bm M cap,
      ∑ z : FullGhostWitness SP sm BP bm M cap x,
        (2:ℝ)^(∑ g,(z g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y z‖ *
          w^(∑ g,((y.2 g).2).1.val)) ≤
      L^(4*W*w*C0/rho)*w^(∑ g,((x.2 g).2).1.val) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc,
    eventually_gt_atTop (0:ℝ)] with L hVisit hL
  intro SG BG instSG instDSG instBG instDBG SP instSP instDSP sm instNZS
    BP instBP instDBP bm instNZB M cap V hV hVW hHarmonic hBig hcount i x
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hmass (g : BG) :
      (∀ p,0 ≤ mu g p) ∧ (∑ p,mu g p) ≤ 2 := by
    apply source_original_memory_physical_tilt_mass_two434 BP bm q N V g (hV g) (hHarmonic g)
    intro p
    exact (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p
      (hVisit _ (hBig g p))).1
  have hh := source_original_evolution_PHYSICAL_G_gamma_row434 SP sm BP bm M cap
    q rho W N i hq hq1 hr hW hg V (fun g => (hV g).le) hVW mu
    (fun g => (hmass g).1) (fun g => (hmass g).2) x
  have hp := source_original_evolution_GAMMA_polynomial434 L W w rho C0
    (Fintype.card BG) hL (zero_le_one.trans hW) hw.1.le hr hcount
  exact hh.trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hw.1.le _))

/-- The same source-regime polynomial bound for the literal symmetric G row
in its original weighted orbit average. No sector-density change is used. -/
theorem eventually_source_original_evolution_TILTED_SYMMETRIC_G_row434
    (c q rho W C0 : ℝ) (hc : 0 < c)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hW : 1 ≤ W) (hg : Real.sqrt q/rho^2 < 1) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (M : ℕ) (cap : BG → ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
      (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hBig : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hcount : (Fintype.card BG:ℝ) ≤ C0*Real.log L)
      (i : ℕ) (F : FullPhysicalOutput SP sm BP bm M → ℂ)
      (hF : ∀ Y ∈ physicalFockOrbitSupport SP sm BP bm M cap,
        ‖F Y‖ ≤ w^(∑ g,((Y.2 g).2).card))
      (X : FullPhysicalOutput SP sm BP bm M)
      (hX : X ∈ physicalFockOrbitSupport SP sm BP bm M cap),
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP bm q N V
    ‖physicalSymmetricVisitGRow SP sm BP bm M cap q rho N i Vs V mu F X‖ ≤
      L^(4*W*w*C0/rho)*w^(∑ g,((X.2 g).2).card) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc,
    eventually_gt_atTop (0:ℝ)] with L hVisit hL
  intro SG BG instSG instDSG instBG instDBG SP instSP instDSP sm instNZS
    BP instBP instDBP bm instNZB M cap Vs V hVs hV hVW hHarmonic hBig hcount i F hF X hX
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hb (g : BG) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p :=
    (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p
      (hVisit _ (hBig g p))).1
  have hmu (g : BG) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hbase : 0 < physicalSourceBaseline BP bm q N g p :=
      lt_of_lt_of_le (by norm_num) (hb g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hV g) hp) hbase)
  have hmass (g : BG) : (∑ p,mu g p) ≤ 2 :=
    (source_original_memory_physical_tilt_mass_two434 BP bm q N V g (hV g)
      (hHarmonic g) (hb g)).2
  have hh := source_original_evolution_ORIGINAL_G_weighted_row434 SP sm BP bm M cap
    q rho W N i hq hq1 hr hW hg Vs hVs V (fun g => (hV g).le) hVW
    mu hmu hmass F hF X hX
  have hp := source_original_evolution_GAMMA_polynomial434 L W w rho C0
    (Fintype.card BG) hL (zero_le_one.trans hW) hw.1.le hr hcount
  exact hh.trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hw.1.le _))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostSectorExchange -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Both genuine Fock endpoint caps are exchanged by the survivor/birth/death
reindexing. In particular no capacity or factorial factor is silently dropped. -/
theorem source_original_evolution_GHOST_sector_exchange434
    (B : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range (B+1),∑ a ∈ Finset.range (B+1),∑ b ∈ Finset.range (B+1),
      if a ≤ j ∧ j-a+b ≤ B then F (j-a) a b else 0) =
    ∑ j ∈ Finset.range (B+1),∑ a ∈ Finset.range (B+1),∑ b ∈ Finset.range (B+1),
      if a ≤ j ∧ j-a+b ≤ B then F (j-a) b a else 0 := by
  classical
  let S : Finset (ℕ × ℕ × ℕ) :=
    ((Finset.range (B+1)) ×ˢ ((Finset.range (B+1)) ×ˢ (Finset.range (B+1)))).filter
      (fun z => z.2.1 ≤ z.1 ∧ z.1-z.2.1+z.2.2 ≤ B)
  let rev (z : ℕ × ℕ × ℕ) := (z.1-z.2.1+z.2.2,z.2.2,z.2.1)
  have hmem (z : ℕ × ℕ × ℕ) :
      z ∈ S ↔ z.1 ≤ B ∧ z.2.1 ≤ B ∧ z.2.2 ≤ B ∧
        z.2.1 ≤ z.1 ∧ z.1-z.2.1+z.2.2 ≤ B := by
    rcases z with ⟨j,a,b⟩
    simp only [S,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
    omega
  have hr (z : ℕ × ℕ × ℕ) (hz : z ∈ S) : rev z ∈ S := by
    rw [hmem] at hz ⊢
    dsimp only [rev]
    omega
  have hinv (z : ℕ × ℕ × ℕ) (hz : z ∈ S) : rev (rev z)=z := by
    have hh := (hmem z).mp hz
    dsimp only [rev]
    apply Prod.ext
    · omega
    · rfl
  have he :
      (∑ z ∈ S,F (z.1-z.2.1) z.2.1 z.2.2) =
      ∑ z ∈ S,F (z.1-z.2.1) z.2.2 z.2.1 := by
    apply Finset.sum_bij (fun z _ => rev z)
    · exact hr
    · intro z hz z' hz' he
      have h := congrArg rev he
      rw [hinv z hz,hinv z' hz'] at h
      exact h
    · intro z hz
      exact ⟨rev z,hr z hz,hinv z hz⟩
    · intro z hz
      have hh := (hmem z).mp hz
      dsimp only [rev]
      congr 1
      omega
  have hsplit (f : ℕ × ℕ × ℕ → ℝ) :
      (∑ z ∈ (Finset.range (B+1)) ×ˢ ((Finset.range (B+1)) ×ˢ (Finset.range (B+1))),f z) =
      ∑ j ∈ Finset.range (B+1),∑ a ∈ Finset.range (B+1),∑ b ∈ Finset.range (B+1),f (j,a,b) := by
    rw [Finset.sum_product (Finset.range (B+1))
      ((Finset.range (B+1)) ×ˢ (Finset.range (B+1))) f]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_product (Finset.range (B+1)) (Finset.range (B+1))
      (fun z : ℕ × ℕ => f (j,z))
  simp only [S,Finset.sum_filter] at he
  rw [hsplit,hsplit] at he
  exact he
end Green64Analytic.CorrelationSquare

end

end

