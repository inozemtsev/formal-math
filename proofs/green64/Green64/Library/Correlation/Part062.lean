module

public import Green64.Library.Weights.Part093
public import Green64.Library.Weights.Part090
public import Green64.Library.Weights.Part087
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.GetD
public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part044

@[expose] public section

/-!
# Correlation / Part062

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredRootPaddedFlat -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_root_PADDED_G_FLAT434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H F X =
    ∑ z : SourceOriginalForestGIndex434 SP sm BP bm J ell cap,
      sourceOriginalForestGFlatCoefficient434 SP sm BP bm J ell cap q rho N i Vs V mu X z *
        F (physicalFockProjection SP sm BP bm (J+ell) cap z.2.1)
          (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T z.1 z.2.2) := by
  unfold sourceOriginalRootPaddedG434
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
theorem source_original_root_PADDED_E_FLAT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H F X =
    ∑ z : SourceOriginalForestEIndex434 SP sm BP bm J ell m cap patterns,
      sourceOriginalForestEFlatCoefficient434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k X z *
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns z.1 o k z.2)
          (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns z.1 z.2) := by
  unfold sourceOriginalRootPaddedE434
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

/-! ## SourceOriginalUnfilteredRootFunctionalLinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


theorem source_original_root_PADDED_G_SUM434
    {I : Type} [Fintype I] (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F : I → Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => ∑ a : I,F a Y H') X =
    ∑ a : I,sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H (F a) X := by
  simp_rw [source_original_root_PADDED_G_FLAT434,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem source_original_root_PADDED_E_SUM434
    {I : Type} [Fintype I] (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F : I → Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H (fun Y H' => ∑ a : I,F a Y H') X =
    ∑ a : I,sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H (F a) X := by
  simp_rw [source_original_root_PADDED_E_FLAT434,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem source_original_root_FUNCTIONAL_SUM434
    {I : Type} [Fintype I]
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : I → Output → List (Option ℕ) → ℂ)
    (n start : ℕ) (Y : Output) (H : List (Option ℕ)) :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (fun out H' => ∑ a : I,F a out H') n start Y H =
    ∑ a : I,sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (F a) n start Y H := by
  induction n generalizing start Y H with
  | zero =>
    exact source_original_root_PADDED_G_SUM434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H F Y
  | succ n ih =>
    let C := fun (a : I) (out : Output) (ht : List (Option ℕ)) =>
      if (∑ g : BG,(out.2 g).2.card)≤T then
        sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T (F a) n (start+1) out ht else 0
    let E := fun (a : I) (yg : Output) (hg : List (Option ℕ)) =>
      if (∑ g : BG,(yg.2 g).2.card)≤T then
        sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu
          (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
          zeta theta (physicalAlternatingSign start) k hg (C a) yg else 0
    have hc :
        (fun (out : Output) (ht : List (Option ℕ)) =>
          if (∑ g : BG,(out.2 g).2.card)≤T then
            sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T
              (fun out H' => ∑ a : I,F a out H') n (start+1) out ht else 0) =
        (fun out ht => ∑ a : I,C a out ht) := by
      funext out ht
      by_cases hh : (∑ g : BG,(out.2 g).2.card)≤T
      · simp only [if_pos hh,C,ih]
      · simp only [if_neg hh,C,Finset.sum_const_zero]
    have he (yg : Output) (hg : List (Option ℕ)) :
        (if (∑ g : BG,(yg.2 g).2.card)≤T then
          sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k hg
            (fun out ht => ∑ a : I,C a out ht) yg else 0) =
        ∑ a : I,E a yg hg := by
      by_cases hh : (∑ g : BG,(yg.2 g).2.card)≤T
      · simp only [if_pos hh,E]
        exact source_original_root_PADDED_E_SUM434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
          zeta theta (physicalAlternatingSign start) k hg C yg
      · simp only [if_neg hh,E,Finset.sum_const_zero]
    simp only [sourceOriginalRootFunctionalChain434]
    rw [hc]
    have hcont :
        (fun yg hg => if (∑ g : BG,(yg.2 g).2.card)≤T then
          sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k hg
            (fun out ht => ∑ a : I,C a out ht) yg else 0) =
        (fun yg hg => ∑ a : I,E a yg hg) := by
      funext yg hg
      exact he yg hg
    rw [hcont,source_original_root_PADDED_G_SUM434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPhaseChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Actual global slot-phase localization, in the original chronological
source chain. Every local phase remains inside its original orbit mean;
the offset counts fixed potential positions, not performed births. -/
theorem source_original_root_ACTUAL_PHASE_CHAIN434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (phi : ℕ → Option ℕ → ℂ) (F : Output → ℂ)
    (n start : ℕ) (Y : Output) (H : List (Option ℕ)) :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T
      (fun out H' => sourceOriginalRootListPhase434 phi 0 H' * F out) n start Y H =
    sourceOriginalRootListPhase434 phi 0 H *
      sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T phi F n start H.length Y := by
  induction n generalizing start Y H with
  | zero =>
    exact source_original_root_PADDED_G_PHASE434 SP sm BP bm J ell cap
      q rho N start T Vs V mu phi H F Y
  | succ n ih =>
    let o := physicalAlternatingSign start
    let K' := memoryOrientationK BP J ell m patterns K o
    let C := sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T phi F n (start+1)
    let EE := fun (offset : ℕ) =>
      sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
        (fun _ _ => True)
        (fun x z => sourceOriginalRootListPhase434 phi offset
          (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
        q rho Vs V mu K T zeta theta o k (C (offset+Fintype.card BG*(J+ell)))
    have hE (yg : Output) (hg : List (Option ℕ)) :
        (if (∑ g : BG,(yg.2 g).2.card)≤T then
          sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K' zeta theta o k hg
            (fun out ht => if (∑ g : BG,(out.2 g).2.card)≤T then
              sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu K zeta theta k N T
                (fun out H' => sourceOriginalRootListPhase434 phi 0 H' * F out)
                n (start+1) out ht else 0) yg else 0) =
          sourceOriginalRootListPhase434 phi 0 hg * EE hg.length yg := by
      have hf :
          (fun (out : Output) (ht : List (Option ℕ)) =>
            if (∑ g : BG,(out.2 g).2.card)≤T then
              sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu K zeta theta k N T
                (fun out H' => sourceOriginalRootListPhase434 phi 0 H' * F out)
                n (start+1) out ht else 0) =
          (fun out ht => if (∑ g : BG,(out.2 g).2.card)≤T then
            sourceOriginalRootListPhase434 phi 0 ht * C ht.length out else 0) := by
        funext out ht
        rw [ih]
      rw [hf]
      have heq :=
        source_original_root_PADDED_E_LENGTH_CONSTANT434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K' zeta theta o k hg
          (fun len out ht => if (∑ g : BG,(out.2 g).2.card)≤T then
            sourceOriginalRootListPhase434 phi 0 ht * C len out else 0) yg
      rw [heq]
      have hh := source_original_root_PADDED_E_PHASE434 SP sm BP bm J ell m cap patterns
        q rho T Vs V mu K zeta theta o k phi hg
        (C (hg.length+Fintype.card BG*(J+ell))) yg
      have hmask :
          (fun (out : Output) (ht : List (Option ℕ)) =>
            if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T out then
              sourceOriginalRootListPhase434 phi 0 ht *
                C (hg.length+Fintype.card BG*(J+ell)) out else 0) =
          (fun out ht => if (∑ g : BG,(out.2 g).2.card)≤T then
              sourceOriginalRootListPhase434 phi 0 ht *
                C (hg.length+Fintype.card BG*(J+ell)) out else 0) := by
        funext out ht
        by_cases ho : (∑ g : BG,(out.2 g).2.card)≤T <;>
          simp [sourceOriginalUnfilteredIdealOLD434,ho]
      rw [hmask] at hh
      by_cases hy : (∑ g : BG,(yg.2 g).2.card)≤T <;>
        simpa only [sourceOriginalUnfilteredIdealOLD434,hy,ite_true,ite_false,K',EE] using hh
    simp only [sourceOriginalRootFunctionalChain434,sourceOriginalRootPhaseGEChain434]
    calc
      _ = sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H
          (fun yg hg => sourceOriginalRootListPhase434 phi 0 hg * EE hg.length yg) Y := by
        apply congrArg (fun f : Output → List (Option ℕ) → ℂ =>
          sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H f Y)
        funext yg hg
        exact hE yg hg
      _ = sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H
          (fun yg hg => sourceOriginalRootListPhase434 phi 0 hg *
            EE (H.length+Fintype.card BG*T) yg) Y :=
        source_original_root_PADDED_G_LENGTH_CONSTANT434 SP sm BP bm J ell cap
          q rho N start T Vs V mu H
          (fun len yg hg => sourceOriginalRootListPhase434 phi 0 hg * EE len yg) Y
      _ = _ := source_original_root_PADDED_G_PHASE434 SP sm BP bm J ell cap
        q rho N start T Vs V mu phi H (EE (H.length+Fintype.card BG*T)) Y
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPinnedContinuation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

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

/-- Original conditional average bound on EVERY physical output, including
zero fibres. No finite type on physical output or probability on histories. -/
theorem source_original_root_ORBIT_BOUND_ALL434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hmu : ∀ g p,0 < mu g p)
    (f : State → ℂ) (B : Output → ℝ) (hB : ∀ X,0≤B X)
    (hf : ∀ x,‖f x‖ ≤ B (physicalFockProjection SP sm BP bm (J+ell) cap x))
    (X : Output) :
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X‖ ≤ B X := by
  by_cases hX : X ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  · exact source_original_evolution_ORBIT_pointwise434 SP sm BP bm (J+ell) cap
      Vs mu hVs hmu f B hf X hX
  · have hm : physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X=0 := by
      unfold physicalOrbitMass
      apply Finset.sum_eq_zero
      intro x hx
      exfalso
      apply hX
      change X ∈ Finset.image (physicalFockProjection SP sm BP bm (J+ell) cap) Finset.univ
      exact Finset.mem_image.mpr ⟨x,Finset.mem_univ x,(Finset.mem_filter.mp hx).2⟩
    simpa [fullPhysicalOrbitAverage,hm] using hB X

/-- A pin-restricted E row permits a continuation depending on the entire
current witness. Uniformity of the continuation envelope is sufficient;
no independence of its updated register is assumed. -/
theorem source_original_root_E_PINNED_CONTINUATION_LOCAL434
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ)
    (w C q rho : ℝ) (hw : 0≤w) (hC : 0≤C)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : State)
    (extra : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (continuation : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ)
    (hcont : ∀ z,‖continuation z‖ ≤ C *
      w^(∑ g,((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z).2 g).2.card)) :
    ‖∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,
      if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
        (∀ g,∀ i ∈ Q g,sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns x z g i =
          some (pin g i)) ∧ extra z then
        sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x z * continuation z else 0‖ ≤
    C * sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
      Q pin w q rho Vs V mu K zeta theta o k x := by
  rw [sourceOriginalForestEPinnedRow434,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z hz
  simp only [source_original_root_E_LABEL_PIN_EXACT434]
  by_cases hp : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
      sourceOriginalForestBigFramePins434 BP bm (J+ell) cap x.2
        (sourceBigShared J ell m (patterns z.1)) Q z.2.2.1.tauBig pin z.2.2.1.bigChoice
  · by_cases he : extra z
    · simp only [hp.1,hp.2,he, and_self,ite_true,norm_mul]
      calc
        _ ≤ ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta o k x z‖ *
            (C*w^(∑ g,((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z).2 g).2.card)) :=
          mul_le_mul_of_nonneg_left (hcont z) (norm_nonneg _)
        _ = _ := by ring
    · simp only [hp.1,hp.2,he,and_false,ite_false,ite_true,norm_zero]
      positivity
  · have hn : ¬(sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
        sourceOriginalForestBigFramePins434 BP bm (J+ell) cap x.2
          (sourceBigShared J ell m (patterns z.1)) Q z.2.2.1.tauBig pin z.2.2.1.bigChoice ∧ extra z) :=
      fun hh => hp ⟨hh.1,hh.2.1⟩
    simp only [if_neg hp,if_neg hn,norm_zero,mul_zero,le_refl]

/-- The analogous literal G continuation inequality keeps actual output
and witness multiplicities. The checked doubled-birth row majorizes it. -/
theorem source_original_root_G_PINNED_CONTINUATION_LOCAL434
    (Q : BG → Finset ℕ) (pin : BG → ℕ → ℕ)
    (w C q rho : ℝ) (hw : 0≤w) (hC : 0≤C)
    (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) (x : State)
    (extra : State → FullGhostWitness SP sm BP bm (J+ell) cap x → Prop)
    (continuation : State → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (hcont : ∀ y z,‖continuation y z‖ ≤ C*w^(∑ g,(y.2 g).2.1.val)) :
    ‖∑ y : State,∑ z : FullGhostWitness SP sm BP bm (J+ell) cap x,
      if (∀ g,∀ j ∈ Q g,sourceOriginalRootGLabel434 SP sm BP bm J ell cap x z g j =
        some (pin g j)) ∧ extra y z then
        physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z *
          continuation y z else 0‖ ≤
    C*(∑ y : State,∑ z : FullGhostWitness SP sm BP bm (J+ell) cap x,
      if ∀ g,Q g ⊆ Finset.range (z g).2.1.val ∧
        (∀ j : Fin (z g).2.1.val,j.val ∈ Q g → bm g ((z g).2.2 j).1=pin g j.val) then
        (2:ℝ)^(∑ g,(z g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z‖ *
            w^(∑ g,(y.2 g).2.1.val) else 0) := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y hy
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z hz
  simp only [source_original_root_G_LABEL_PIN_EXACT434]
  by_cases hp : ∀ g,Q g ⊆ Finset.range (z g).2.1.val ∧
      (∀ j : Fin (z g).2.1.val,j.val ∈ Q g → bm g ((z g).2.2 j).1=pin g j.val)
  · by_cases he : extra y z
    · rw [if_pos ⟨hp,he⟩,if_pos hp,norm_mul]
      have htwo : (1:ℝ) ≤ 2^(∑ g,(z g).2.1.val) := one_le_pow₀ (by norm_num)
      calc
        _ ≤ ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z‖ *
            (C*w^(∑ g,(y.2 g).2.1.val)) :=
          mul_le_mul_of_nonneg_left (hcont y z) (norm_nonneg _)
        _ ≤ C*((2:ℝ)^(∑ g,(z g).2.1.val) *
              ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z‖ *
                w^(∑ g,(y.2 g).2.1.val)) := by
          have hh := mul_le_mul_of_nonneg_right htwo
            (mul_nonneg (norm_nonneg (physicalGBranchTerm SP sm BP bm
              (J+ell) cap q rho N i V mu x y z)) (mul_nonneg hC
                (pow_nonneg hw (∑ g,(y.2 g).2.1.val))))
          nlinarith only [hh]
    · rw [if_neg (fun hh => he hh.2),if_pos hp,norm_zero]
      positivity
  · rw [if_neg (fun hh => hp hh.1),if_neg hp,norm_zero,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPinnedOrbit -/

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

def sourceOriginalRootEPinOrbit434
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (extra : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (continuation : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ)
    (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu (fun x =>
    ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,
      if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
        (∀ g,∀ i ∈ Q g,sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns x z g i =
          some (pin g i)) ∧ extra x z then
        sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x z * continuation x z else 0) X

/-- Deterministic adapter from the original ordered pinned E row to its
actual compressed row, uniformly in every physical input. Its ordered
premise is supplied by SOURCE_E_PINNED, not by a forest assumption. -/
theorem source_original_root_E_PINNED_ORBIT_ADAPTER434
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ)
    (w C B q rho : ℝ) (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (hrow : ∀ x : State,sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
      Q pin w q rho Vs V mu K zeta theta o k x ≤ B*w^(∑ g,(x.2 g).2.1.val))
    (extra : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (continuation : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ)
    (hcont : ∀ x z,‖continuation x z‖ ≤ C*
      w^(∑ g,((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z).2 g).2.card))
    (X : Output) :
    ‖sourceOriginalRootEPinOrbit434 SP sm BP bm J ell m cap patterns Q pin
      q rho Vs V mu K zeta theta o k extra continuation X‖ ≤
    (C*B)*w^(∑ g,(X.2 g).2.card) := by
  apply source_original_root_ORBIT_BOUND_ALL434 SP sm BP bm J ell cap Vs mu hVs hmu
    _ (fun Y => (C*B)*w^(∑ g,(Y.2 g).2.card)) (fun _ => by positivity)
  intro x
  rw [source_original_evolution_projection_OLD434]
  calc
    _ ≤ C*sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
        Q pin w q rho Vs V mu K zeta theta o k x :=
      source_original_root_E_PINNED_CONTINUATION_LOCAL434 SP sm BP bm J ell m cap patterns
        Q pin w C q rho hw hC Vs V mu K zeta theta o k x (extra x) (continuation x) (hcont x)
    _ ≤ C*(B*w^(∑ g,(x.2 g).2.1.val)) :=
      mul_le_mul_of_nonneg_left (hrow x) hC
    _ = _ := by ring

def sourceOriginalRootGPinOrbit434
    (Q : BG → Finset ℕ) (pin : BG → ℕ → ℕ)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (extra : (x y : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → Prop)
    (continuation : (x y : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu (fun x =>
    ∑ y : State,∑ z : FullGhostWitness SP sm BP bm (J+ell) cap x,
      if (∀ g,∀ j ∈ Q g,sourceOriginalRootGLabel434 SP sm BP bm J ell cap x z g j =
        some (pin g j)) ∧ extra x y z then
        physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z *
          continuation x y z else 0) X

/-- The actual repeated-state G row with an arbitrary witness-dependent
suffix, proved directly from the inherited pinned physical row. -/
theorem source_original_root_G_PINNED_ORBIT434
    (Q : BG → Finset ℕ) (pin : BG → ℕ → ℕ)
    (q rho W w C delta : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hC : 0 ≤ C) (hd : 0 ≤ delta)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (hAtom : ∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤
      delta*(∑ p : BP g,mu g p))
    (extra : (x y : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → Prop)
    (continuation : (x y : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (hcont : ∀ x y z,‖continuation x y z‖ ≤ C*w^(∑ g,(y.2 g).2.1.val))
    (X : Output) :
    ‖sourceOriginalRootGPinOrbit434 SP sm BP bm J ell cap Q pin
      q rho N i Vs V mu extra continuation X‖ ≤
    (C*(delta^(∑ g,(Q g).card)*Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))) *
      w^(∑ g,(X.2 g).2.card) := by
  apply source_original_root_ORBIT_BOUND_ALL434 SP sm BP bm J ell cap Vs mu hVs hmu
    _ (fun Y => (C*(delta^(∑ g,(Q g).card)*Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))) *
      w^(∑ g,(Y.2 g).2.card)) (fun _ => by positivity)
  intro x
  rw [source_original_evolution_projection_OLD434]
  apply (source_original_root_G_PINNED_CONTINUATION_LOCAL434 SP sm BP bm J ell cap Q pin
    w C q rho hw.le hC N i V mu x (extra x) (continuation x) (hcont x)).trans
  have hh := source_original_forest_PHYSICAL_G_PINNED_ROW434 SP sm BP bm (J+ell) cap
    q rho W w N i hq hq1 hr hW hw hcontrol V hV hVW mu
    (fun g p => (hmu g p).le) hmass Q pin delta hd hAtom x
  have hh' := mul_le_mul_of_nonneg_left hh hC
  simpa only [mul_assoc] using hh'
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPinnedChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sourceOriginalRootPinnedRank434 (kg ke : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,i => kg i
  | n+1,i => sourceOriginalRootPinnedRank434 kg ke n (i+1)+ke i+kg i

def sourceOriginalRootPinnedBudget434 (delta gamma a : ℝ) (kg ke : ℕ → ℕ) : ℕ → ℕ → ℝ
  | 0,i => delta^(kg i)*gamma
  | n+1,i => (sourceOriginalRootPinnedBudget434 delta gamma a kg ke n (i+1)*
      (delta^(ke i)*a))*(delta^(kg i)*gamma)

theorem source_original_root_PINNED_BUDGET_NONNEG434
    (delta gamma a : ℝ) (hd : 0 ≤ delta) (hg : 0 ≤ gamma) (ha : 0 ≤ a)
    (kg ke : ℕ → ℕ) (n i : ℕ) :
    0 ≤ sourceOriginalRootPinnedBudget434 delta gamma a kg ke n i := by
  induction n generalizing i with
  | zero => exact mul_nonneg (pow_nonneg hd _) hg
  | succ n ih =>
    exact mul_nonneg (mul_nonneg (ih _) (mul_nonneg (pow_nonneg hd _) ha))
      (mul_nonneg (pow_nonneg hd _) hg)

theorem source_original_root_PINNED_BUDGET_CLOSED434
    (delta gamma a : ℝ) (kg ke : ℕ → ℕ) (n i : ℕ) :
    sourceOriginalRootPinnedBudget434 delta gamma a kg ke n i =
      delta^(sourceOriginalRootPinnedRank434 kg ke n i)*gamma^(n+1)*a^n := by
  induction n generalizing i with
  | zero => simp [sourceOriginalRootPinnedBudget434,sourceOriginalRootPinnedRank434]
  | succ n ih =>
    simp only [sourceOriginalRootPinnedBudget434,sourceOriginalRootPinnedRank434,ih,
      pow_add,pow_succ]
    ring

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Original physical pinned rows with chronological option-valued history,
local numerical ND, both OLD gates and final G. Pin values may depend on
the complete prior register, including repeats and inactive entries.
The fixed Q sets never depend on representatives or current witnesses. -/
def sourceOriginalRootPinnedGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (QG : ℕ → BG → Finset ℕ) (QE : ℕ → BG → Finset (Fin (J+ell)))
    (pinG : ℕ → List (Option ℕ) → BG → ℕ → ℕ)
    (pinE : ℕ → List (Option ℕ) → BG → Fin (J+ell) → ℕ)
    (extraG : ℕ → List (Option ℕ) → (x y : State) →
      FullGhostWitness SP sm BP bm (J+ell) cap x → Prop)
    (extraE : ℕ → List (Option ℕ) → (x : State) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (terminal : Output → List (Option ℕ) → ℂ) :
    ℕ → ℕ → Output → List (Option ℕ) → ℂ
  | 0,i,Y,H =>
    sourceOriginalRootGPinOrbit434 SP sm BP bm J ell cap (QG i) (pinG i H)
      q rho N i Vs V mu
      (fun x y z => (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup ∧ extraG i H x y z)
      (fun x y z => terminal (physicalFockProjection SP sm BP bm (J+ell) cap y)
        (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)) Y
  | n+1,i,Y,H =>
    sourceOriginalRootGPinOrbit434 SP sm BP bm J ell cap (QG i) (pinG i H)
      q rho N i Vs V mu
      (fun x y z => (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup ∧
        (∑ g,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2.card)≤T ∧ extraG i H x y z)
      (fun x y z =>
        let HG := H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z
        sourceOriginalRootEPinOrbit434 SP sm BP bm J ell m cap patterns (QE i) (pinE i HG)
          q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
          zeta theta (physicalAlternatingSign i) k
          (fun xe ze => (orientedEFreshBirths SP sm BP bm J ell m cap patterns ze).Nodup ∧
            (∑ g,((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns xe
              (physicalAlternatingSign i) k ze).2 g).2.card)≤T ∧ extraE i HG xe ze)
          (fun xe ze => sourceOriginalRootPinnedGEChain434 q rho Vs V mu K zeta theta k N T
            QG QE pinG pinE extraG extraE terminal n (i+1)
            (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns xe (physicalAlternatingSign i) k ze)
            (HG++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns xe ze))
          (physicalFockProjection SP sm BP bm (J+ell) cap y)) Y

/-- Actual physical suffix induction, uniform in EVERY register. The
only E premise is the original ordered pinned-row estimate; the G row
bound is derived from its numerical atom law. No forest/root saving is
a premise, and no history is conditioned upon or renormalized. -/
theorem source_original_root_ACTUAL_PINNED_SUFFIX434
    (q rho W w delta a : ℝ) (N T : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hd : 0 ≤ delta) (ha : 0 ≤ a)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (hAtom : ∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤ delta*(∑ p : BP g,mu g p))
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (hrow : ∀ i Q pin x,
      sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
        Q pin w q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
        zeta theta (physicalAlternatingSign i) k x ≤
      (delta^(∑ g,(Q g).card)*a)*w^(∑ g,(x.2 g).2.1.val))
    (QG : ℕ → BG → Finset ℕ) (QE : ℕ → BG → Finset (Fin (J+ell)))
    (pinG : ℕ → List (Option ℕ) → BG → ℕ → ℕ)
    (pinE : ℕ → List (Option ℕ) → BG → Fin (J+ell) → ℕ)
    (extraG : ℕ → List (Option ℕ) → (x y : State) →
      FullGhostWitness SP sm BP bm (J+ell) cap x → Prop)
    (extraE : ℕ → List (Option ℕ) → (x : State) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (terminal : Output → List (Option ℕ) → ℂ)
    (hterminal : ∀ Y H,‖terminal Y H‖ ≤ w^(∑ g,(Y.2 g).2.card))
    (n i : ℕ) (Y : Output) (H : List (Option ℕ)) :
    ‖sourceOriginalRootPinnedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T QG QE pinG pinE extraG extraE terminal n i Y H‖ ≤
    sourceOriginalRootPinnedBudget434 delta (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)) a
      (fun j => ∑ g,(QG j g).card) (fun j => ∑ g,(QE j g).card) n i *
      w^(∑ g,(Y.2 g).2.card) := by
  induction n generalizing i Y H with
  | zero =>
    have hh := source_original_root_G_PINNED_ORBIT434 SP sm BP bm J ell cap
      (QG i) (pinG i H) q rho W w 1 delta N i hq hq1 hr hW hw (by norm_num) hd hcontrol
      Vs V mu hVs hV hVW hmu hmass hAtom
      (fun x y z => (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup ∧ extraG i H x y z)
      (fun x y z => terminal (physicalFockProjection SP sm BP bm (J+ell) cap y)
        (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z))
      (fun x y z => by
        simpa only [one_mul,source_original_evolution_projection_OLD434] using
          hterminal (physicalFockProjection SP sm BP bm (J+ell) cap y)
            (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)) Y
    simpa only [sourceOriginalRootPinnedGEChain434,sourceOriginalRootPinnedBudget434,one_mul] using hh
  | succ n ih =>
    let C := sourceOriginalRootPinnedBudget434 delta
      (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)) a
      (fun j => ∑ g,(QG j g).card) (fun j => ∑ g,(QE j g).card) n (i+1)
    have hC : 0 ≤ C := source_original_root_PINNED_BUDGET_NONNEG434 _ _ _ hd
      (Real.exp_pos _).le ha _ _ _ _
    have hEC : 0 ≤ C*(delta^(∑ g,(QE i g).card)*a) :=
      mul_nonneg hC (mul_nonneg (pow_nonneg hd _) ha)
    change ‖sourceOriginalRootGPinOrbit434 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _‖ ≤ _
    apply (source_original_root_G_PINNED_ORBIT434 SP sm BP bm J ell cap
      (QG i) (pinG i H) q rho W w (C*(delta^(∑ g,(QE i g).card)*a)) delta N i
      hq hq1 hr hW hw hEC hd hcontrol Vs V mu hVs hV hVW hmu hmass hAtom _ _ _ Y).trans_eq
    · rfl
    · intro x y z
      dsimp only
      have hh := source_original_root_E_PINNED_ORBIT_ADAPTER434 SP sm BP bm J ell m cap patterns
        (QE i) (pinE i (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z))
        w C (delta^(∑ g,(QE i g).card)*a) q rho hw.le hC
        (mul_nonneg (pow_nonneg hd _) ha) Vs V mu hVs hmu
        (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
        zeta theta (physicalAlternatingSign i) k (hrow i _ _)
        (fun xe ze => (orientedEFreshBirths SP sm BP bm J ell m cap patterns ze).Nodup ∧
          (∑ g,((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns xe
            (physicalAlternatingSign i) k ze).2 g).2.card)≤T ∧
          extraE i (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z) xe ze)
        (fun xe ze => sourceOriginalRootPinnedGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T QG QE pinG pinE extraG extraE terminal n (i+1)
          (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns xe (physicalAlternatingSign i) k ze)
          ((H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)++
            sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns xe ze))
        (fun xe ze => ih (i+1)
          (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns xe (physicalAlternatingSign i) k ze)
          ((H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)++
            sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns xe ze))
        (physicalFockProjection SP sm BP bm (J+ell) cap y)
      simpa only [source_original_evolution_projection_OLD434] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPinnedSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sourceOriginalRootPinnedRowBudget434
    {SG BG : Type} [Fintype SG] [Fintype BG] [DecidableEq BG]
    (Vs : SG → ℝ) (V : BG → ℝ) (blockA blockB : Finset BG)
    (ell m conductor : ℕ) (q rho w xi : ℝ) : ℝ :=
  (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
    sourceOriginalMemoryRawComparisonCap434 blockA blockB m conductor xi nu)*
  (∏ g : SG,memorySmallRowConstant q (Vs g) ell)*
  (∏ g : BG,w^(ell+m)*(4:ℝ)^(ell+m)*
    (memoryPromotionDampingConstant rho (ell+m)*
      ((max 1 (V g)⁻¹)^(ell+m)*(2:ℝ)^(ell+m))))

theorem source_original_root_PINNED_ROW_BUDGET_NONNEG434
    {SG BG : Type} [Fintype SG] [Fintype BG] [DecidableEq BG]
    (Vs : SG → ℝ) (V : BG → ℝ) (blockA blockB : Finset BG)
    (ell m conductor : ℕ) (q rho w xi : ℝ)
    (hVs : ∀ g,0 < Vs g) (hq : q ≤ 1) (hr : rho ≤ 1) (hw : 0 ≤ w) :
    0 ≤ sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi := by
  have hs : Real.sqrt q ≤ 1 := by simpa using Real.sqrt_le_sqrt hq
  have hqs : 0 ≤ 1-Real.sqrt q := sub_nonneg.mpr hs
  have hrs : 0 ≤ 1-rho := sub_nonneg.mpr hr
  have hpromo : 0 ≤ memoryPromotionDampingConstant rho (ell+m) := by
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  unfold sourceOriginalRootPinnedRowBudget434
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.sum_nonneg (fun nu _ =>
        source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m conductor xi nu)
    · apply Finset.prod_nonneg
      intro g hg
      unfold memorySmallRowConstant
      have hh := hVs g
      positivity
  · apply Finset.prod_nonneg
    intro g hg
    have hh : 0 ≤ max 1 (V g)⁻¹ := le_trans (by norm_num) (le_max_left _ _)
    positivity

/-- Uniform actual SOURCE pinned suffix at the original moving tilt and
OLD cutoff. Both the numerical atom law and the full canonical E row
are derived from accepted source theorems. No collision/forest/operator
saving is assumed. Registers may repeat numerical values or contain none. -/
theorem eventually_source_original_root_SOURCE_PINNED_SUFFIX434
    (c vmin q rho W w : ℝ) (hc : 0 < c) (hv : 0 < vmin)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hW : 1 ≤ W) (hw : 1 ≤ w)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p∈P g}),NeZero p.val]
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p∈P g},1/(p.val:ℝ)=V g)
      (hBig : ∀ g (p : {p : ℕ // p∈P g}),Real.exp (L^c) ≤ (p.val:ℝ))
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
      (conductor : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
      (hhA : ∀ nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (cap : G → ℕ),
    let BP := fun g => {p : ℕ // p∈P g}
    let bm := fun (g : G) (p : BP g) => p.val
    let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ conductor hA hB xi
    let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
    let delta := 2/(vmin*Real.exp (L^c))
    let a := sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi
    ∀ (QG : ℕ → G → Finset ℕ) (QE : ℕ → G → Finset (Fin (J+ell)))
      (pinG : ℕ → List (Option ℕ) → G → ℕ → ℕ)
      (pinE : ℕ → List (Option ℕ) → G → Fin (J+ell) → ℕ)
      (extraG : ℕ → List (Option ℕ) →
        (x y : FullPhysicalState SP sm BP bm (J+ell) cap) →
        FullGhostWitness SP sm BP bm (J+ell) cap x → Prop)
      (extraE : ℕ → List (Option ℕ) →
        (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
        FullOrientedSourceChoice SP sm BP bm J ell m cap pat x → Prop)
      (zeta theta : ℝ) (k : ℤ) (n i : ℕ)
      (Y : FullPhysicalOutput SP sm BP bm (J+ell)) (H : List (Option ℕ)),
    ‖sourceOriginalRootPinnedGEChain434 SP sm BP bm J ell m cap pat
      q rho Vs V mu K zeta theta k (2*Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))
      QG QE pinG pinE extraG extraE (fun out _ => physicalVacuum SP sm BP bm J ell out) n i Y H‖ ≤
    delta^(sourceOriginalRootPinnedRank434
      (fun j => ∑ g,(QG j g).card) (fun j => ∑ g,(QE j g).card) n i)*
      (Real.exp (4*W*w*(Fintype.card G:ℝ)/rho))^(n+1)*a^n*w^(∑ g,(Y.2 g).2.card) := by
  filter_upwards [eventually_source_original_forest_SOURCE_E_PINNED434
    c vmin q rho hc hv hq hq1 hr hr1,
    eventually_source_original_forest_TILT_LAWS434 c vmin q hc hv hq.le hq1.le] with L hE hTilt
  intro SG instSG instDSG SP instSP instDSP sm instSM G instG instDG P instP
    V hV hVW hHarmonic hBig Vs hVs blockA blockB J ell m hmJ conductor hA hB xi hhA hhB hxi cap
  dsimp only
  intro QG QE pinG pinE extraG extraE zeta theta k n i Y H
  let BP := fun g => {p : ℕ // p∈P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ conductor hA hB xi
  let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
  let delta := 2/(vmin*Real.exp (L^c))
  let a := sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi
  obtain ⟨hmu,hmass,hAtom⟩ := hTilt BP bm V (fun g => Subtype.val_injective) hV hHarmonic hBig
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hd : 0 ≤ delta := by dsimp [delta]; positivity
  have ha : 0 ≤ a := source_original_root_PINNED_ROW_BUDGET_NONNEG434
    Vs V blockA blockB ell m conductor q rho w xi hVs hq1.le hr1.le hw0.le
  have hrow (j : ℕ) (Q : G → Finset (Fin (J+ell))) (pin : G → Fin (J+ell) → ℕ)
      (x : FullPhysicalState SP sm BP bm (J+ell) cap) :
      sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap pat
        Q pin w q rho Vs V mu (memoryOrientationK BP J ell m pat K (physicalAlternatingSign j))
        zeta theta (physicalAlternatingSign j) k x ≤
      (delta^(∑ g,(Q g).card)*a)*w^(∑ g,(x.2 g).2.1.val) := by
    have ho : physicalAlternatingSign j=1 ∨ physicalAlternatingSign j= -1 := by
      unfold physicalAlternatingSign
      split_ifs <;> simp
    exact hE SP sm P V hV hHarmonic hBig Vs hVs blockA blockB J ell m hmJ conductor hA hB xi
      hhA hhB hxi cap Q pin w hw zeta theta (physicalAlternatingSign j) k ho x
  have hterminal (Y : FullPhysicalOutput SP sm BP bm (J+ell)) (_H : List (Option ℕ)) :
      ‖physicalVacuum SP sm BP bm J ell Y‖ ≤ w^(∑ g,(Y.2 g).2.card) := by
    unfold physicalVacuum
    split_ifs
    · simpa only [norm_one] using (one_le_pow₀ hw : (1:ℝ) ≤ w^(∑ g,(Y.2 g).2.card))
    · simp only [norm_zero]
      positivity
  have hh := source_original_root_ACTUAL_PINNED_SUFFIX434 SP sm BP bm J ell m cap pat
    q rho W w delta a (2*Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))
    hq.le hq1.le hr hW hw0 hd ha hcontrol Vs V mu hVs
    (fun g => (hv.trans_le (hV g)).le) hVW hmu hmass hAtom K zeta theta k hrow
    QG QE pinG pinE extraG extraE (fun out _ => physicalVacuum SP sm BP bm J ell out)
    hterminal n i Y H
  rw [source_original_root_PINNED_BUDGET_CLOSED434] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootRowPolynomial -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem source_original_root_PINNED_BUDGET_FACTOR434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (Vs : SG → ℝ) (V : G → ℝ) (blockA blockB : Finset G)
    (ell m conductor : ℕ) (q rho w xi : ℝ) :
    sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi =
      w^((ell+m)*Fintype.card G)*
        sourceOriginalUnfilteredEdgeBudget434 ell m q rho 2 Vs V
          (sourceOriginalMemoryRawComparisonCap434 blockA blockB m conductor xi) := by
  unfold sourceOriginalRootPinnedRowBudget434 sourceOriginalUnfilteredEdgeBudget434
  simp only [mul_assoc,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←pow_mul]
  ring

/-- The high-rank positive row prefactor is polynomial at original
source group counts. It has no active-slot/J dependence. -/
theorem source_original_root_PINNED_BUDGET_POLYNOMIAL434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (ell m Cq Cxi Q : ℕ)
    (q rho v C0 w L xi : ℝ) (Vs : SG → ℝ) (V : G → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hv : 0 < v) (hC0 : 0 ≤ C0) (hw : 1 ≤ w) (hL : 2 ≤ L) (hxi : 0 < xi)
    (hVs : ∀ g,v ≤ Vs g) (hV : ∀ g,v ≤ V g)
    (hSmall : (Fintype.card SG:ℝ) ≤ C0*Real.log L)
    (hBig : (Fintype.card G:ℝ) ≤ C0*Real.log L)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ C0*Real.log L)
    (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi) :
    sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m Q q rho w xi ≤
      L^(sourceOriginalUnfilteredEdgeExponent434 ell m Cq Cxi q rho v C0 1+
        ((ell+m:ℕ):ℝ)*C0*Real.log w) := by
  let C := sourceOriginalUnfilteredEdgeBudget434 ell m q rho 2 Vs V
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
  let kappa := sourceOriginalUnfilteredEdgeExponent434 ell m Cq Cxi q rho v C0 1
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hC0' : 0 ≤ C := source_original_edge_BUDGET_NONNEG434 ell m q rho 2 Vs V _
    hq hq1 hr1 (by norm_num) (fun g => hv.trans_le (hVs g))
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
  have hpoly := source_original_edge_CANONICAL_BUDGET_POLYNOMIAL434 blockA blockB ell m Cq Cxi Q
    q rho v C0 1 L xi Vs V hq hq1 hr hr1 hv hC0 (by norm_num) hL hxi
    hVs hV hSmall hBig hGroups hQ hXi
  have hsq : C^2 ≤ (L^kappa)^2 := by
    have he : L^(2*kappa)=(L^kappa)^2 := by
      convert Real.rpow_mul_natCast hLp.le kappa 2 using 1 <;> norm_num <;> ring
    have hpoly' : C^2 ≤ L^(2*kappa) := by
      simpa only [one_pow,mul_one] using hpoly
    rw [he] at hpoly'
    exact hpoly'
  have hC : C ≤ L^kappa := by
    have hh := Real.rpow_pos_of_pos hLp kappa
    nlinarith
  have hW := source_original_edge_RATIO_POLYNOMIAL434 L w C0 (ell+m) (Fintype.card G) hL1 hw hBig
  rw [source_original_root_PINNED_BUDGET_FACTOR434]
  calc
    _ ≤ L^(((ell+m:ℕ):ℝ)*C0*Real.log w)*L^kappa :=
      mul_le_mul hW hC hC0' (Real.rpow_nonneg hLp.le _)
    _ = _ := by rw [←Real.rpow_add hLp]; congr 1; dsimp only [kappa]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSlotEnumeration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalRootGSlots434 (G : Type) [Fintype G] (T : ℕ) : List (G × Fin T) :=
  (Finset.univ : Finset G).toList.product (List.ofFn (fun i : Fin T => i))

def sourceOriginalRootESlots434 (G : Type) [Fintype G] (M : ℕ) : List (G × Fin M) :=
  (Finset.univ : Finset G).toList.product (Finset.univ : Finset (Fin M)).toList

theorem source_original_root_G_SLOTS_ND434 (G : Type) [Fintype G] (T : ℕ) :
    (sourceOriginalRootGSlots434 G T).Nodup := by
  apply List.Nodup.product (Finset.nodup_toList _)
  rw [List.nodup_ofFn]
  exact fun _ _ h => h

theorem source_original_root_E_SLOTS_ND434 (G : Type) [Fintype G] (M : ℕ) :
    (sourceOriginalRootESlots434 G M).Nodup :=
  List.Nodup.product (Finset.nodup_toList _) (Finset.nodup_toList _)

theorem source_original_root_G_SLOTS_MEM434 (G : Type) [Fintype G] (T : ℕ)
    (g : G) (j : Fin T) : (g,j)∈sourceOriginalRootGSlots434 G T := by
  simp [sourceOriginalRootGSlots434]

theorem source_original_root_E_SLOTS_MEM434 (G : Type) [Fintype G] (M : ℕ)
    (g : G) (j : Fin M) : (g,j)∈sourceOriginalRootESlots434 G M := by
  simp [sourceOriginalRootESlots434]

theorem source_original_root_ENUM_MAP_GETD434
    {A : Type} [DecidableEq A] (l : List A) (a : A) (ha : a∈l)
    (f : A → Option ℕ) :
    (l.map f).getD (l.idxOf a) none=f a := by
  simp [List.getD,List.getElem?_map,List.getElem?_idxOf ha]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap

/-- The G enumeration is the original group order followed by numerical
newborn position order. It is fixed independently of every witness. -/
theorem source_original_root_G_PAD_ENUM434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) :
    sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z =
      (sourceOriginalRootGSlots434 BG T).map
        (fun a => sourceOriginalRootGLabel434 SP sm BP bm J ell cap x z a.1 a.2.val) := by
  simp [sourceOriginalRootGPad434,sourceOriginalRootGSlots434,List.product,
    List.map_flatMap,sourceOriginalRootPadPrefix434,List.map_ofFn,
    sourceOriginalRootGLabel434,Function.comp_def]

/-- E slots are fixed CANONICAL pre-tau positions; the numerical readout
remains the true target after tau. -/
theorem source_original_root_E_PAD_ENUM434 (x : State)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z =
      (sourceOriginalRootESlots434 BG (J+ell)).map
        (fun a => sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns x z a.1 a.2) := by
  simp [sourceOriginalRootEPad434,sourceOriginalRootESlots434,List.product,
    List.map_flatMap,List.map_map,Function.comp_def]

theorem source_original_root_G_SLOT_READ434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) (g : BG) (j : Fin T) :
    (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z).getD
      ((sourceOriginalRootGSlots434 BG T).idxOf (g,j)) none =
      sourceOriginalRootGLabel434 SP sm BP bm J ell cap x z g j.val := by
  rw [source_original_root_G_PAD_ENUM434]
  simp [List.getD,List.getElem?_map,
    List.getElem?_idxOf (source_original_root_G_SLOTS_MEM434 BG T g j)]

theorem source_original_root_E_SLOT_READ434 (x : State)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) (g : BG) (j : Fin (J+ell)) :
    (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z).getD
      ((sourceOriginalRootESlots434 BG (J+ell)).idxOf (g,j)) none =
      sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns x z g j := by
  rw [source_original_root_E_PAD_ENUM434]
  simp [List.getD,List.getElem?_map,
    List.getElem?_idxOf (source_original_root_E_SLOTS_MEM434 BG (J+ell) g j)]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootBatchPins -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_root_FOREST_EDGE_ZERO_ONE434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H : List (Option ℕ)) (i : Fin A) :
    sourceOriginalRootForestEdge434 p H i=0 ∨ sourceOriginalRootForestEdge434 p H i=1 := by
  unfold sourceOriginalRootForestEdge434
  cases hp : p i with
  | none => exact Or.inr rfl
  | some j => simp only [Option.elim]; split_ifs <;> simp

theorem source_original_root_FOREST_BATCH_NONZERO_ONE434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (o : ℕ) (H : List (Option ℕ))
    (h : sourceOriginalRootForestBatch434 p o H ≠ 0) :
    sourceOriginalRootForestBatch434 p o H=1 := by
  unfold sourceOriginalRootForestBatch434 at h ⊢
  apply Finset.prod_eq_one
  intro i hi
  by_cases hin : o ≤ i.val ∧ i.val < H.length
  · rw [if_pos hin]
    rcases source_original_root_FOREST_EDGE_ZERO_ONE434 p H i with hz|ho
    · exfalso
      exact h (Finset.prod_eq_zero_iff.mpr ⟨i,Finset.mem_univ _,by rw [if_pos hin,hz]⟩)
    · exact ho
  · rw [if_neg hin]

theorem source_original_root_FOREST_BATCH_UNIT_BOUND434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (o : ℕ) (H : List (Option ℕ)) :
    ‖sourceOriginalRootForestBatch434 p o H‖ ≤ 1 := by
  by_cases hz : sourceOriginalRootForestBatch434 p o H=0
  · simp [hz]
  · rw [source_original_root_FOREST_BATCH_NONZERO_ONE434 p o H hz]
    simp

/-- Every selected child of a surviving numerical-ND batch has an active
numeric parent in the PRIOR register. Repeated prior values are allowed.
A same-batch parent or an inactive parent forces the whole row to zero. -/
theorem source_original_root_BATCH_NONZERO_PIN434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H B : List (Option ℕ))
    (hND : (B.filterMap id).Nodup)
    (i : Fin A) (j : Fin i.val) (hp : p i=some j)
    (hi0 : H.length ≤ i.val) (hi : i.val < (H++B).length)
    (h : sourceOriginalRootForestBatch434 p H.length (H++B) ≠ 0) :
    j.val < H.length ∧ ∃ v : ℕ,
      H.getD j.val none=some v ∧ (H++B).getD i.val none=some v := by
  have hj : j.val < H.length := by
    by_contra hn
    exact h (source_original_root_SAME_BATCH_ZERO434 p H B hND i j hp (by omega) hi)
  have hedge : sourceOriginalRootForestEdge434 p (H++B) i ≠ 0 := by
    intro hz
    apply h
    unfold sourceOriginalRootForestBatch434
    exact Finset.prod_eq_zero_iff.mpr ⟨i,Finset.mem_univ _,by rw [if_pos ⟨hi0,hi⟩,hz]⟩
  refine ⟨hj,?_⟩
  cases hv : H.getD j.val none with
  | none =>
    have hpnone : (H++B).getD j.val none=none := by
      rw [List.getD_append H B none j.val hj,hv]
    exact False.elim (hedge (source_original_root_FOREST_EDGE_PARENT_NONE434 p (H++B) i j hp hpnone))
  | some v =>
    refine ⟨v,rfl,?_⟩
    have hpv : (H++B).getD j.val none=some v := by
      rw [List.getD_append H B none j.val hj,hv]
    rw [source_original_root_FOREST_EDGE_NUMERIC434 p (H++B) i j hp v hpv] at hedge
    by_contra hn
    exact hedge (if_neg hn)

/-- The value passed to the pinned row is a total register read. Its
arbitrary zero fallback is used only on branches already annihilated. -/
theorem source_original_root_BATCH_NONZERO_PIN_VALUE434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H B : List (Option ℕ))
    (hND : (B.filterMap id).Nodup)
    (i : Fin A) (j : Fin i.val) (hp : p i=some j)
    (hi0 : H.length ≤ i.val) (hi : i.val < (H++B).length)
    (h : sourceOriginalRootForestBatch434 p H.length (H++B) ≠ 0) :
    (H++B).getD i.val none=some ((H.getD j.val none).getD 0) := by
  obtain ⟨hj,v,hv,hchild⟩ :=
    source_original_root_BATCH_NONZERO_PIN434 p H B hND i j hp hi0 hi h
  simpa only [hv,Option.getD_some] using hchild
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualForestPins -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalRootParentAt434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (j : ℕ) : Option ℕ :=
  if h : j < A then (p ⟨j,h⟩).map Fin.val else none

def sourceOriginalRootPinAt434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (j : ℕ) (H : List (Option ℕ)) : ℕ :=
  ((sourceOriginalRootParentAt434 p j).bind (fun b => H.getD b none)).getD 0

def sourceOriginalRootForestQE434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M offset : ℕ) (g : G) : Finset (Fin M) :=
  Finset.univ.filter (fun i =>
    (sourceOriginalRootParentAt434 p (offset+(sourceOriginalRootESlots434 G M).idxOf (g,i))).isSome)

def sourceOriginalRootForestPinE434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M offset : ℕ)
    (H : List (Option ℕ)) (g : G) (i : Fin M) : ℕ :=
  sourceOriginalRootPinAt434 p (offset+(sourceOriginalRootESlots434 G M).idxOf (g,i)) H

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap

/-- Every original constrained E summand supplies the actual pinned-row
Q and numerical values. Q uses fixed pre-tau potential addresses and is
independent of the current representative, permutation and witness. -/
theorem source_original_root_ACTUAL_FOREST_E_PINS434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (H : List (Option ℕ))
    (hA : H.length+Fintype.card BG*(J+ell) ≤ A)
    (x : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hND : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup)
    (hBatch : sourceOriginalRootForestBatch434 p H.length
      (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z) ≠ 0) :
    ∀ g,∀ i∈sourceOriginalRootForestQE434 p BG (J+ell) H.length g,
      sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns x z g i =
      some (sourceOriginalRootForestPinE434 p BG (J+ell) H.length H g i) := by
  intro g i hi
  let t := (sourceOriginalRootESlots434 BG (J+ell)).idxOf (g,i)
  have ht : t < Fintype.card BG*(J+ell) := by
    have hh := List.idxOf_lt_length_iff.mpr (source_original_root_E_SLOTS_MEM434 BG (J+ell) g i)
    simpa [t,sourceOriginalRootESlots434,List.product,List.length_flatMap] using hh
  have hai : H.length+t < A := by omega
  let a : Fin A := ⟨H.length+t,hai⟩
  have hsel : (p a).isSome := by
    have hh : (sourceOriginalRootParentAt434 p (H.length+t)).isSome :=
      (Finset.mem_filter.mp hi).2
    unfold sourceOriginalRootParentAt434 at hh
    rw [dif_pos hai] at hh
    simpa only [Option.isSome_map] using hh
  cases hp : p a with
  | none => simp [hp] at hsel
  | some j =>
    have hPadND : ((sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z).filterMap id).Nodup :=
      (source_original_root_E_PAD_BIRTHS434 SP sm BP bm J ell m cap patterns x z).nodup_iff.mpr hND
    have ha0 : H.length ≤ a.val := by dsimp [a]; omega
    have ha1 : a.val < (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z).length := by
      simp only [List.length_append,source_original_root_E_PAD_LENGTH434]
      dsimp [a]
      omega
    have hh := source_original_root_BATCH_NONZERO_PIN_VALUE434 p H
      (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z)
      hPadND a j hp ha0 ha1 hBatch
    rw [List.getD_append_right H _ none a.val ha0] at hh
    have hsub : a.val-H.length=t := by dsimp [a]; omega
    rw [hsub,source_original_root_E_SLOT_READ434] at hh
    change _=some (sourceOriginalRootPinAt434 p (H.length+t) H)
    unfold sourceOriginalRootPinAt434 sourceOriginalRootParentAt434
    rw [dif_pos hai]
    change _=some (((p a).map Fin.val).bind (fun b => H.getD b none) |>.getD 0)
    simpa only [hp,Option.map_some,Option.bind_some] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualGhostPins -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000


def sourceOriginalRootForestQGFin434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (T offset : ℕ) (g : G) : Finset (Fin T) :=
  Finset.univ.filter (fun i =>
    (sourceOriginalRootParentAt434 p (offset+(sourceOriginalRootGSlots434 G T).idxOf (g,i))).isSome)

def sourceOriginalRootForestQG434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (T offset : ℕ) (g : G) : Finset ℕ :=
  (sourceOriginalRootForestQGFin434 p G T offset g).image Fin.val

def sourceOriginalRootForestPinG434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (T offset : ℕ)
    (H : List (Option ℕ)) (g : G) (j : ℕ) : ℕ :=
  if h : j < T then
    sourceOriginalRootPinAt434 p (offset+(sourceOriginalRootGSlots434 G T).idxOf (g,⟨j,h⟩)) H
  else 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap

/-- Actual G birth positions, including harmless oversized padding:
a nonzero locally-ND batch supplies the fixed original pinned G row. -/
theorem source_original_root_ACTUAL_FOREST_G_PINS434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (T : ℕ) (H : List (Option ℕ))
    (hA : H.length+Fintype.card BG*T ≤ A)
    (x : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (hND : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup)
    (hBatch : sourceOriginalRootForestBatch434 p H.length
      (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z) ≠ 0) :
    ∀ g,∀ j∈sourceOriginalRootForestQG434 p BG T H.length g,
      sourceOriginalRootGLabel434 SP sm BP bm J ell cap x z g j =
      some (sourceOriginalRootForestPinG434 p BG T H.length H g j) := by
  intro g j hj
  obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp hj
  subst j
  let t := (sourceOriginalRootGSlots434 BG T).idxOf (g,i)
  have ht : t < Fintype.card BG*T := by
    have hh := List.idxOf_lt_length_iff.mpr (source_original_root_G_SLOTS_MEM434 BG T g i)
    simpa [t,sourceOriginalRootGSlots434,List.product,List.length_flatMap] using hh
  have hai : H.length+t < A := by omega
  let a : Fin A := ⟨H.length+t,hai⟩
  have hsel : (p a).isSome := by
    have hh : (sourceOriginalRootParentAt434 p (H.length+t)).isSome :=
      (Finset.mem_filter.mp hi).2
    unfold sourceOriginalRootParentAt434 at hh
    rw [dif_pos hai] at hh
    simpa only [Option.isSome_map] using hh
  cases hp : p a with
  | none => simp [hp] at hsel
  | some j =>
    have hPadND := source_original_root_G_PAD_NODUP434 SP sm BP bm J ell cap T x z hND
    have ha0 : H.length ≤ a.val := by dsimp [a]; omega
    have ha1 : a.val < (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z).length := by
      simp only [List.length_append,source_original_root_G_PAD_LENGTH434]
      dsimp [a]
      omega
    have hh := source_original_root_BATCH_NONZERO_PIN_VALUE434 p H
      (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)
      hPadND a j hp ha0 ha1 hBatch
    rw [List.getD_append_right H _ none a.val ha0] at hh
    have hsub : a.val-H.length=t := by dsimp [a]; omega
    rw [hsub,source_original_root_G_SLOT_READ434] at hh
    unfold sourceOriginalRootForestPinG434
    rw [dif_pos i.isLt]
    change _=some (sourceOriginalRootPinAt434 p (H.length+t) H)
    unfold sourceOriginalRootPinAt434 sourceOriginalRootParentAt434
    rw [dif_pos hai]
    change _=some (((p a).map Fin.val).bind (fun b => H.getD b none) |>.getD 0)
    simpa only [hp,Option.map_some,Option.bind_some] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootBatchRows -/

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


/-- Exact original E batch row as an original pinned row with an extra
zero-one mask. Both numerical pins and the inactive-parent zero case are
derived from the retained local ND; no reweighting is performed. -/
theorem source_original_root_E_BATCH_PINNED_ROW434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (H : List (Option ℕ))
    (hA : H.length+Fintype.card BG*(J+ell) ≤ A)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (mask : Output → Prop) [DecidablePred mask] (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k H
      (fun out H' => sourceOriginalRootForestBatch434 p H.length H'*
        (if mask out then F out H' else 0)) X =
    sourceOriginalRootEPinOrbit434 SP sm BP bm J ell m cap patterns
      (sourceOriginalRootForestQE434 p BG (J+ell) H.length)
      (sourceOriginalRootForestPinE434 p BG (J+ell) H.length H)
      q rho Vs V mu K zeta theta o k
      (fun x z => (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup ∧
        mask (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z) ∧
        sourceOriginalRootForestBatch434 p H.length
          (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z) ≠ 0)
      (fun x z => F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z)) X := by
  unfold sourceOriginalRootPaddedE434 sourceOriginalRootEPinOrbit434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  unfold sourceOrientedPhysicalChoices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only
  by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z
  · by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup
    · by_cases hm : mask (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      · by_cases hb : sourceOriginalRootForestBatch434 p H.length
          (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z)=0
        · simp only [if_pos hl,if_pos hn,if_pos hm,hb,zero_mul,ne_eq,not_true_eq_false,
            and_false,if_false,mul_zero]
        · have hp := source_original_root_ACTUAL_FOREST_E_PINS434 SP sm BP bm J ell m cap patterns
            p H hA x z hn hb
          have hB := source_original_root_FOREST_BATCH_NONZERO_ONE434 p H.length _ hb
          rw [if_pos hl,if_pos hn,if_pos hm,if_pos ⟨hl,hp,hn,hm,hb⟩,hB,one_mul]
      · simp [hl,hn,hm]
    · simp [hl,hn]
  · simp [hl]

/-- The G analogue retains all original signed witnesses. Padding is
only a readout; no branch is removed by comparison of signed operators. -/
theorem source_original_root_G_BATCH_PINNED_ROW434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (T : ℕ) (H : List (Option ℕ))
    (hA : H.length+Fintype.card BG*T ≤ A)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (mask : Output → Prop) [DecidablePred mask] (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun out H' => sourceOriginalRootForestBatch434 p H.length H'*
        (if mask out then F out H' else 0)) X =
    sourceOriginalRootGPinOrbit434 SP sm BP bm J ell cap
      (sourceOriginalRootForestQG434 p BG T H.length)
      (sourceOriginalRootForestPinG434 p BG T H.length H)
      q rho N i Vs V mu
      (fun x y z => (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup ∧
        mask (physicalFockProjection SP sm BP bm (J+ell) cap y) ∧
        sourceOriginalRootForestBatch434 p H.length
          (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z) ≠ 0)
      (fun x y z => F (physicalFockProjection SP sm BP bm (J+ell) cap y)
        (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)) X := by
  unfold sourceOriginalRootPaddedG434 sourceOriginalRootGPinOrbit434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only
  by_cases hn : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup
  · by_cases hm : mask (physicalFockProjection SP sm BP bm (J+ell) cap y)
    · by_cases hb : sourceOriginalRootForestBatch434 p H.length
        (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)=0
      · simp [hn,hm,hb]
      · have hp := source_original_root_ACTUAL_FOREST_G_PINS434 SP sm BP bm J ell cap
          p T H hA x z hn hb
        have hB := source_original_root_FOREST_BATCH_NONZERO_ONE434 p H.length _ hb
        rw [if_pos hn,if_pos hm,if_pos ⟨hp,hn,hm,hb⟩,hB,one_mul]
    · simp [hn,hm]
  · simp [hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootBatchRowBound -/

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


theorem source_original_root_E_BATCH_ROW_BOUND434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (H : List (Option ℕ))
    (hA : H.length+Fintype.card BG*(J+ell) ≤ A)
    (w C B q rho : ℝ) (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (hrow : ∀ x : State,sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
      (sourceOriginalRootForestQE434 p BG (J+ell) H.length)
      (sourceOriginalRootForestPinE434 p BG (J+ell) H.length H)
      w q rho Vs V mu K zeta theta o k x ≤ B*w^(∑ g,(x.2 g).2.1.val))
    (mask : Output → Prop) [DecidablePred mask] (F : Output → List (Option ℕ) → ℂ)
    (hF : ∀ Y H',H'.length=H.length+Fintype.card BG*(J+ell) →
      ‖F Y H'‖ ≤ C*w^(∑ g,(Y.2 g).2.card)) (X : Output) :
    ‖sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k H
      (fun out H' => sourceOriginalRootForestBatch434 p H.length H'*
        (if mask out then F out H' else 0)) X‖ ≤ (C*B)*w^(∑ g,(X.2 g).2.card) := by
  rw [source_original_root_E_BATCH_PINNED_ROW434 SP sm BP bm J ell m cap patterns p H hA]
  apply source_original_root_E_PINNED_ORBIT_ADAPTER434 SP sm BP bm J ell m cap patterns
    _ _ w C B q rho hw hC hB Vs V mu hVs hmu K zeta theta o k hrow
  intro x z
  apply hF
  simp only [List.length_append,source_original_root_E_PAD_LENGTH434]

theorem source_original_root_G_BATCH_ROW_BOUND434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (T : ℕ) (H : List (Option ℕ))
    (hA : H.length+Fintype.card BG*T ≤ A)
    (q rho W w C delta : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hC : 0 ≤ C) (hd : 0 ≤ delta)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (hAtom : ∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤
      delta*(∑ p : BP g,mu g p))
    (mask : Output → Prop) [DecidablePred mask] (F : Output → List (Option ℕ) → ℂ)
    (hF : ∀ Y H',H'.length=H.length+Fintype.card BG*T →
      ‖F Y H'‖ ≤ C*w^(∑ g,(Y.2 g).2.card)) (X : Output) :
    ‖sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun out H' => sourceOriginalRootForestBatch434 p H.length H'*
        (if mask out then F out H' else 0)) X‖ ≤
    (C*(delta^(∑ g,(sourceOriginalRootForestQG434 p BG T H.length g).card)*
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)))*w^(∑ g,(X.2 g).2.card) := by
  rw [source_original_root_G_BATCH_PINNED_ROW434 SP sm BP bm J ell cap p T H hA]
  apply source_original_root_G_PINNED_ORBIT434 SP sm BP bm J ell cap
    _ _ q rho W w C delta N i hq hq1 hr hW hw hC hd hcontrol Vs V mu hVs hV hVW hmu hmass hAtom
  intro x y z
  have hh := hF (physicalFockProjection SP sm BP bm (J+ell) cap y)
    (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)
    (by simp only [List.length_append,source_original_root_G_PAD_LENGTH434])
  simpa only [source_original_evolution_projection_OLD434] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootEnumerationCount -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 500000

def sourceOriginalRootEnumerationEquiv434
    {S : Type} [BEq S] [LawfulBEq S] (l : List S) (hND : l.Nodup) (hAll : ∀ a,a∈l) :
    S ≃ Fin l.length where
  toFun a := ⟨l.idxOf a,List.idxOf_lt_length_iff.mpr (hAll a)⟩
  invFun i := l[i.val]
  left_inv a := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hAll a))
  right_inv i := by
    apply Fin.ext
    exact hND.getElem_inj_iff.mp (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hAll l[i.val])))

theorem source_original_root_ENUMERATION_SUM434
    {S : Type} [Fintype S] [BEq S] [LawfulBEq S]
    (l : List S) (hND : l.Nodup) (hAll : ∀ a,a∈l) (f : ℕ → ℕ) :
    (∑ a : S,f (l.idxOf a))=∑ j∈Finset.range l.length,f j := by
  have hh := (sourceOriginalRootEnumerationEquiv434 l hND hAll).sum_comp (fun j => f j.val)
  rw [Fin.sum_univ_eq_sum_range] at hh
  exact hh

def sourceOriginalRootAddressCount434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (o width : ℕ) : ℕ :=
  ∑ j∈Finset.range width,if (sourceOriginalRootParentAt434 p (o+j)).isSome then 1 else 0

theorem source_original_root_E_COUNT_ADDRESSES434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M o : ℕ) :
    (∑ g,(sourceOriginalRootForestQE434 p G M o g).card)=
      sourceOriginalRootAddressCount434 p o (Fintype.card G*M) := by
  unfold sourceOriginalRootForestQE434
  simp only [Finset.card_filter]
  have hh := source_original_root_ENUMERATION_SUM434 (sourceOriginalRootESlots434 G M)
    (source_original_root_E_SLOTS_ND434 G M)
    (fun a => source_original_root_E_SLOTS_MEM434 G M a.1 a.2)
    (fun j => if (sourceOriginalRootParentAt434 p (o+j)).isSome then 1 else 0)
  rw [Fintype.sum_prod_type] at hh
  have hlen : (sourceOriginalRootESlots434 G M).length=Fintype.card G*M := by
    simp [sourceOriginalRootESlots434,List.product,List.length_flatMap]
  simpa only [hlen,sourceOriginalRootAddressCount434] using hh

theorem source_original_root_G_COUNT_ADDRESSES434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (T o : ℕ) :
    (∑ g,(sourceOriginalRootForestQG434 p G T o g).card)=
      sourceOriginalRootAddressCount434 p o (Fintype.card G*T) := by
  have hc (g : G) : (sourceOriginalRootForestQG434 p G T o g).card=
      (sourceOriginalRootForestQGFin434 p G T o g).card := by
    exact Finset.card_image_of_injective _ Fin.val_injective
  simp only [hc,sourceOriginalRootForestQGFin434,Finset.card_filter]
  have hh := source_original_root_ENUMERATION_SUM434 (sourceOriginalRootGSlots434 G T)
    (source_original_root_G_SLOTS_ND434 G T)
    (fun a => source_original_root_G_SLOTS_MEM434 G T a.1 a.2)
    (fun j => if (sourceOriginalRootParentAt434 p (o+j)).isSome then 1 else 0)
  rw [Fintype.sum_prod_type] at hh
  have hlen : (sourceOriginalRootGSlots434 G T).length=Fintype.card G*T := by
    simp [sourceOriginalRootGSlots434,List.product,List.length_flatMap]
  simpa only [hlen,sourceOriginalRootAddressCount434] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeFiltered -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
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

theorem source_original_edge_COLUMN_MONO434
    (keep env : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (hkeep : ∀ st z,keep st z → env st z)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (Y : Output) :
    sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k Y ≤
    sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      env q rho Vs V mu K zeta theta o k Y := by
  apply Finset.sum_le_sum
  intro st _
  apply mul_le_mul_of_nonneg_left _ (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu st).le
  apply Finset.sum_le_sum
  intro z _
  split_ifs with h h'
  · exact le_rfl
  · exact False.elim (h' ⟨h.1,hkeep st z h.2⟩)
  · exact norm_nonneg _
  · exact le_rfl

theorem source_original_edge_DENSITY_COLUMN_MONO434
    (keep env : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (hkeep : ∀ st z,keep st z → env st z)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (Y : Output) :
    sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k Y ≤
    sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap patterns
      env q rho Vs V mu K zeta theta o k Y := by
  apply Finset.sum_le_sum
  intro st _
  apply mul_le_mul_of_nonneg_left _ (source_original_memory_FULL_density_mass_nonneg434
    SP sm BP bm J ell cap Vs V mu hVs hV hmu st)
  apply Finset.sum_le_sum
  intro z _
  split_ifs with h h'
  · exact le_rfl
  · exact False.elim (h' ⟨h.1,hkeep st z h.2⟩)
  · exact norm_nonneg _
  · exact le_rfl

/-- Exact source-orbit row bound from local absolute rows, in plain pi.
The bound may depend on membership of st in the fixed source orbit. -/
theorem source_original_edge_PAIR_ROW_OF_LOCAL434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (X : Output) (B : ℝ)
    (hrow : ∀ st,physicalFockProjection SP sm BP bm (J+ell) cap st=X →
      sourceOriginalMemoryOriginalFilteredRow434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k st ≤ B) :
    (∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y) ≤
    B*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X := by
  let s := sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V
  have hs := source_original_memory_sector_density_pos434 SP sm BP bm J ell V hV X
  apply le_of_mul_le_mul_left (a:=s X) ?_ hs
  dsimp only [s]
  rw [Finset.mul_sum]
  simp_rw [source_original_edge_PAIR_SECTOR434]
  rw [source_original_memory_FILTERED_pair_target_sum434]
  have hm : (∑ st : State,if physicalFockProjection SP sm BP bm (J+ell) cap st=X then
      sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs V mu st else 0) =
      physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X*s X := by
    have hh := source_original_memory_sector_density_orbit_mass434 SP sm BP bm J ell cap Vs V mu X
    simp only [Finset.sum_filter] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro st _
    by_cases hx : physicalFockProjection SP sm BP bm (J+ell) cap st=X <;>
      simp only [hx,ite_true,ite_false,sourceOriginalMemoryFullDensityMass434]
  calc
    _ ≤ B*(∑ st : State,if physicalFockProjection SP sm BP bm (J+ell) cap st=X then
        sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs V mu st else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro st _
      by_cases hx : physicalFockProjection SP sm BP bm (J+ell) cap st=X
      · rw [if_pos hx,if_pos hx]
        exact (mul_le_mul_of_nonneg_left (hrow st hx)
          (source_original_memory_FULL_density_mass_nonneg434 SP sm BP bm J ell cap Vs V mu
            hVs hV hmu st)).trans_eq (mul_comm _ _)
      · simp only [hx,ite_false,mul_zero,le_refl]
    _ = _ := by rw [hm]; ring

/-- Schur adapter for literal witness phases and an actual witness envelope.
The row/column hypotheses are mathematical obligations, not source assumptions. -/
theorem source_original_edge_FILTERED_PHASE_ENERGY434
    (keep env : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (hkeep : ∀ st z,keep st z → env st z)
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (hphase : ∀ st z,‖phase st z‖ ≤ 1)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (A B : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ X,(∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        env q rho Vs V mu K zeta theta o k X Y) ≤
      A*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X)
    (hcol : ∀ Y,sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
        env q rho Vs V mu K zeta theta o k Y ≤
      B*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y)
    (F : Output → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
        (sourceOriginalUnfilteredEdgePhasedLocal434 SP sm BP bm J ell m cap patterns
          keep phase q rho Vs V mu K zeta theta o k F)) ≤
      A*B*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let S := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  let M := physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu
  let P := sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
    env q rho Vs V mu K zeta theta o k
  have hM (X) : 0 ≤ M X := Finset.sum_nonneg
    (fun st _ => (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu st).le)
  have hP (X Y) : 0 ≤ P X Y := source_original_edge_PAIR_NONNEG434
    SP sm BP bm J ell m cap patterns env q rho Vs V mu hVs hmu K zeta theta o k X Y
  have hc (Y) (_ : Y ∈ S) : (∑ X ∈ S,P X Y) ≤ B*M Y := by
    dsimp only [P,S]
    rw [source_original_edge_PAIR_SOURCE_SUM434]
    exact hcol Y
  have ht (X) (_ : X ∈ S) := source_original_edge_ORBIT_DOMINATION434
    SP sm BP bm J ell m cap patterns env q rho Vs V mu hVs hV hmu K zeta theta o k F
    (sourceOriginalUnfilteredEdgePhasedLocal434 SP sm BP bm J ell m cap patterns
      keep phase q rho Vs V mu K zeta theta o k F)
    (source_original_edge_PHASED_LOCAL_DOMINATION434 SP sm BP bm J ell m cap patterns
      keep env hkeep phase hphase q rho Vs V mu K zeta theta o k F) X
  exact source_original_finite_density_kernel_energy434 S M hM P hP A B hA
    (fun X _ => hrow X) hc F _ ht
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeRareMargins -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
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

/-- Source-gated promotion remains rare after full repeated-state orbit
compression. No target support or distinct-OLD condition is used. -/
theorem source_original_edge_PROMOTION_PLAIN_ROW434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (gate : Output → Prop)
    (hkeep : ∀ st z,keep st z → gate (physicalFockProjection SP sm BP bm (J+ell) cap st) ∧
      ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (B : ℝ) (hB : 0 ≤ B)
    (hrare : ∀ st,gate (physicalFockProjection SP sm BP bm (J+ell) cap st) →
      sourceOriginalMemoryOriginalEPromotionRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st ≤ B) (X : Output) :
    (∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y) ≤
      B*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X := by
  apply source_original_edge_PAIR_ROW_OF_LOCAL434 SP sm BP bm J ell m cap patterns
    keep q rho Vs V mu hVs hV hmu K zeta theta o k X B
  intro st _
  by_cases hg : gate (physicalFockProjection SP sm BP bm (J+ell) cap st)
  · apply le_trans _ (hrare st hg)
    apply Finset.sum_le_sum
    intro z _
    split_ifs with h h'
    · exact le_rfl
    · exact False.elim (h' ⟨h.1,(hkeep st z h.2).2⟩)
    · exact norm_nonneg _
    · exact le_rfl
  · have hz : ∀ z,¬keep st z := fun z h => hg (hkeep st z h).1
    simpa only [sourceOriginalMemoryOriginalFilteredRow434,hz,and_false,ite_false,
      Finset.sum_const_zero] using hB

/-- Target-gated store-only column via full joint-K reverse promotion,
then a one-step density transfer. BOTH arbitrary repeated-state carriers
and arbitrary witness restrictions are retained. -/
theorem source_original_edge_STORE_PLAIN_COLUMN434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (gate : Output → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p) (hr : 0 ≤ rho)
    (Rv : ℝ) (hRv : 1 ≤ Rv) (hVR : ∀ g,V g ≤ Rv) (hiR : ∀ g,(V g)⁻¹ ≤ Rv)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (hkeep : ∀ st z,keep st z →
      gate (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z) ∧
      (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
      (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
    (B : ℝ) (hB : 0 ≤ B)
    (hrare : ∀ st,gate (physicalFockProjection SP sm BP bm (J+ell) cap st) →
      sourceOriginalMemoryOriginalEPromotionRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu (fun nu aux s t => K nu aux t s) zeta theta (-o) k st ≤ B)
    (Y : Output) :
    sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k Y ≤
      B*Rv^((ell+m)*Fintype.card BG)*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y := by
  apply source_original_edge_FILTERED_COLUMN_TRANSFER434 SP sm BP bm J ell m cap patterns
    keep q rho Vs V mu hVs hV hmu Rv hRv hVR hiR K zeta theta o k Y B
  by_cases hg : gate Y
  · calc
      _ ≤ sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap patterns
        (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
          (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
        q rho Vs V mu K zeta theta o k Y :=
        source_original_edge_DENSITY_COLUMN_MONO434 SP sm BP bm J ell m cap patterns keep _
          (fun st z h => (hkeep st z h).2) q rho Vs V mu hVs hV hmu K zeta theta o k Y
      _ ≤ _ := source_original_memory_STORE_ONLY_density_column_of_reverse_row434
        SP sm BP bm J ell m cap patterns q rho Vs V mu hVs hV hmu hr K zeta theta o k Y B
        (fun st hx => hrare st (by rw [hx]; exact hg))
  · have hz : sourceOriginalMemoryOriginalFilteredDensityColumn434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k Y=0 := by
      apply Finset.sum_eq_zero
      intro st _
      have he : (∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st,
          if (sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧
              sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z=Y) ∧ keep st z
          then ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta o k st z‖ else 0)=0 := by
        apply Finset.sum_eq_zero
        intro z _
        apply if_neg
        intro h
        exact hg (h.1.2 ▸ (hkeep st z h.2).1)
      rw [he,mul_zero]
    rw [hz]
    exact mul_nonneg hB (source_original_memory_FULL_density_orbit_nonneg434
      SP sm BP bm J ell cap Vs V mu hVs hV hmu Y)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeDirty -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_edge_CLEAN_IFF434
    (st : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st) :
    memorySourceCleanChoice SP sm BP bm J ell m cap patterns st z ↔
    (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
      (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty) := by
  simp only [memorySourceCleanChoice,←Finset.not_nonempty_iff_eq_empty,forall_and,not_exists]
  exact and_comm

theorem source_original_edge_LITERAL_DIRTY_SPLIT434
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun st z => ¬memorySourceCleanChoice SP sm BP bm J ell m cap patterns st z)
      phase q rho Vs V mu K T zeta theta o k F X =
    sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun _ z => ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
      phase q rho Vs V mu K T zeta theta o k F X +
    sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun _ z => (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
        (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty))
      phase q rho Vs V mu K T zeta theta o k F X := by
  unfold sourceOriginalUnfilteredEdgeSeenErasedPhase434
  rw [←source_original_evolution_ORBIT_add434]
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext st
  unfold sourceOriginalUnfilteredEdgePhasedLocal434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  simp only [source_original_edge_CLEAN_IFF434]
  by_cases hp : ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty <;>
    by_cases hs : ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty <;>
    simp [hp,hs]

theorem source_original_edge_ENERGY_ADD434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p) (f g : Output → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu (fun X => f X+g X) ≤
    2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu f +
    2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu g := by
  unfold sourceOriginalUnfilteredIdealOrbitEnergy434
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X hX
  have hs := pow_le_pow_left₀ (norm_nonneg (f X+g X)) (norm_add_le (f X) (g X)) 2
  have hp : ‖f X+g X‖^2 ≤ 2*‖f X‖^2+2*‖g X‖^2 := by
    nlinarith only [hs,sq_nonneg (‖f X‖-‖g X‖)]
  have hh := mul_le_mul_of_nonneg_left hp
    (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu X hX).le
  convert hh using 1 <;> ring

/-- Finite actual DIRTY estimate in plain pi from the TWO literal rare
promotion rows. These rarity obligations are discharged by the source
geometry separately; no reachable-state hypothesis is introduced. -/
theorem source_original_edge_LITERAL_DIRTY_FINITE434
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (hphase : ∀ st z,‖phase st z‖ ≤ 1)
    (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (Rv : ℝ) (hRv : 1 ≤ Rv) (hVR : ∀ g,V g ≤ Rv) (hiR : ∀ g,(V g)⁻¹ ≤ Rv)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu)
    (B : ℝ) (hB : 0 ≤ B)
    (hforward : ∀ st,sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (physicalFockProjection SP sm BP bm (J+ell) cap st) →
      sourceOriginalMemoryOriginalEPromotionRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K o) zeta theta o k st ≤ B)
    (hreverse : ∀ st,sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (physicalFockProjection SP sm BP bm (J+ell) cap st) →
      sourceOriginalMemoryOriginalEPromotionRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu (fun nu aux s t => memoryOrientationK BP J ell m patterns K o nu aux t s)
        zeta theta (-o) k st ≤ B) (F : Output → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
        (fun st z => ¬memorySourceCleanChoice SP sm BP bm J ell m cap patterns st z)
        phase q rho Vs V mu K T zeta theta o k F) ≤
    4*sourceOriginalUnfilteredEdgeBudget434 ell m q rho R Vs V Kcap*B *
      Rv^((ell+m)*Fintype.card BG)*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let C := sourceOriginalUnfilteredEdgeBudget434 ell m q rho R Vs V Kcap
  let D := Rv^((ell+m)*Fintype.card BG)
  let gate := sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
  let K' := memoryOrientationK BP J ell m patterns K o
  let pp := fun (st : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st) =>
    ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty
  let ps := fun (st : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st) =>
    (¬pp st z) ∧ (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty)
  let kp := fun st z => sourceOriginalUnfilteredEdgeLiteralKeep434 SP sm BP bm J ell m cap patterns T o k st z ∧ pp st z
  let ks := fun st z => sourceOriginalUnfilteredEdgeLiteralKeep434 SP sm BP bm J ell m cap patterns T o k st z ∧ ps st z
  let P := sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns pp
    phase q rho Vs V mu K T zeta theta o k F
  let S := sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns ps
    phase q rho Vs V mu K T zeta theta o k F
  have hC : 0 ≤ C := source_original_edge_BUDGET_NONNEG434 ell m q rho R Vs V Kcap
    hq hq1 hr1 (le_trans zero_le_one hR) hVs hK0
  have hK' := source_original_edge_ORIENTATION_CAP434 BP J ell m patterns K Kcap hK o
  have hfullcol (Y) : sourceOriginalUnfilteredEdgePlainColumn434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K' zeta theta o k Y ≤
      C*D*physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu Y :=
    source_original_edge_FULL_PLAIN_COLUMN434 SP sm BP bm J ell m cap patterns
      q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic
      Rv hRv hVR hiR K' zeta theta o k Kcap hK0 hK' Y
  have hp : sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu P ≤
      B*(C*D)*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
    apply source_original_edge_FILTERED_PHASE_ENERGY434 SP sm BP bm J ell m cap patterns
      kp kp (fun _ _ h => h) phase hphase q rho Vs V mu hVs hV hmu K' zeta theta o k B (C*D) hB
    · intro X
      exact source_original_edge_PROMOTION_PLAIN_ROW434 SP sm BP bm J ell m cap patterns kp gate
        (fun st z h => ⟨h.1.1,h.2⟩) q rho Vs V mu hVs hV hmu K' zeta theta o k B hB hforward X
    · intro Y
      exact (source_original_edge_COLUMN_MONO434 SP sm BP bm J ell m cap patterns kp
        (fun _ _ => True) (fun _ _ _ => trivial) q rho Vs V mu hVs hmu K' zeta theta o k Y).trans
        (hfullcol Y)
  have hs : sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu S ≤
      C*(B*D)*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
    apply source_original_edge_FILTERED_PHASE_ENERGY434 SP sm BP bm J ell m cap patterns
      ks ks (fun _ _ h => h) phase hphase q rho Vs V mu hVs hV hmu K' zeta theta o k C (B*D) hC
    · intro X
      exact source_original_edge_FILTERED_PLAIN_ROW434 SP sm BP bm J ell m cap patterns ks
        q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic K' zeta theta o k Kcap hK0 hK' X
    · intro Y
      exact source_original_edge_STORE_PLAIN_COLUMN434 SP sm BP bm J ell m cap patterns ks gate
        q rho Vs V mu hVs hV hmu hr.le Rv hRv hVR hiR K' zeta theta o k
        (fun st z h => ⟨h.1.2.2,h.2⟩) B hB hreverse Y
  have he := source_original_edge_ENERGY_ADD434 SP sm BP bm J ell cap Vs mu hVs hmu P S
  have hsplit : (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun st z => ¬memorySourceCleanChoice SP sm BP bm J ell m cap patterns st z)
      phase q rho Vs V mu K T zeta theta o k F) = fun X => P X+S X := by
    funext X
    exact source_original_edge_LITERAL_DIRTY_SPLIT434 SP sm BP bm J ell m cap patterns
      phase q rho Vs V mu K T zeta theta o k F X
  rw [hsplit]
  exact he.trans (by dsimp only [C,D] at hp hs ⊢; nlinarith only [hp,hs])
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeSourceRare -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Original physical geometric rarity for the COMPLETE E row with any
joint K cap. Arbitrary m and J are allowed: no cfg.tmax hypothesis. This
is an eventual source theorem, not a norm-smallness assumption. -/
theorem eventually_source_original_edge_COMPLETE_RARE_ROW434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Ck q rho : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (J m : ℕ) (cap : G → ℕ)
      (st : FullPhysicalState
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern G J m)
      (K : SourcePatternK (fun g => {p : ℕ // p ∈ data.Tb g}) J ell m patterns)
      (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
      (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalMemoryOriginalEPromotionRow434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap patterns q rho data.Vsmall data.Vbig mu K zeta theta o k st ≤
    sourceOriginalUnfilteredEdgeBudget434 ell m q rho 2 data.Vsmall data.Vbig Kcap *
      (((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ)/(((J+ell).choose ell:ℝ)^(Fintype.card ι))) := by
  filter_upwards [eventually_source_original_memory_PHYSICAL_BIG_rare_promotion_row434
    cfg ell Ck q rho hq.le hq1.le hr hr1] with L hRare
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    J m cap st hSmallUpper hBigLower hHarmonic Nu instNu patterns K Kcap hK0 hK
    zeta theta o k ho hk0 hk
  let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
    (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let eps := (((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ)/(((J+ell).choose ell:ℝ)^(Fintype.card ι)))
  let Cb := ∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
    ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m)))
  have hVs : ∀ g,0 < data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0 < data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hh := source_original_memory_ORIGINAL_E_promotion_outer_bound434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
    J ell m cap patterns q rho data.Vsmall data.Vbig hq hq1 hVs hVb hHarmonic
    mu K zeta theta o k ho st Kcap hK0 hK (eps*Cb)
    (fun nu aux bs bt => hRare x Y Hprime data sep J m cap st
      hSmallUpper hBigLower hHarmonic (patterns nu) aux bs bt o k ho hk0 hk)
  exact hh.trans_eq (by dsimp only [sourceOriginalUnfilteredEdgeBudget434,eps,Cb]; ring)
end Green64Analytic.CorrelationSquare

end

end

