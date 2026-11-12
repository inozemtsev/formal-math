module

public import Green64.Library.Weights.LiteralProjectedDyadicEnvelope
public import Green64.Library.Weights.Part100

@[expose] public section

/-!
# Weights / BigPatternLift

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualBigPatternLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The existing literal BIG-to-all map, as an embedding. -/
def b604ActualBigGroupEmbedding434 (r : ℕ) (L : ℝ) :
    sourceNativeOriginalBigType434 r L ↪ sourceOriginalPAllGroupType r L where
  toFun := sourceNativeOriginalBigToAll434 r L
  inj' := by
    intro g h he
    exact Subtype.ext (congrArg (fun z : sourceOriginalPAllGroupType r L => z.val) he)

/-- The original labelled position is unchanged by the actual group lift. -/
def b604ActualBigProbeEmbedding434 (r : ℕ) (L : ℝ) (m : ℕ) :
    (sourceNativeOriginalBigType434 r L × Fin m) ↪
      (sourceOriginalPAllGroupType r L × Fin m) :=
  Function.Embedding.prodMap (b604ActualBigGroupEmbedding434 r L) (Function.Embedding.refl _)

/-- Lift the original BIG pattern into the complete actual P family.
No SMALL probe is added and no original BIG label is deleted. -/
def b604ActualLiftedPattern434 (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m) :
    SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m :=
  (nu.1.map (b604ActualBigProbeEmbedding434 r L m),
   nu.2.map (b604ActualBigProbeEmbedding434 r L m))

@[simp] theorem b604_actual_probe_lift_mem434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (A : Finset (sourceNativeOriginalBigType434 r L × Fin m))
    (g : sourceNativeOriginalBigType434 r L) (i : Fin m) :
    (sourceNativeOriginalBigToAll434 r L g,i)∈A.map (b604ActualBigProbeEmbedding434 r L m) ↔
      (g,i)∈A := by
  change b604ActualBigProbeEmbedding434 r L m (g,i)∈A.map _ ↔ _
  simp

/-- Exact original probe cardinalities, hence its inclusion-exclusion
sign and four-sign parity phase, are preserved. -/
theorem b604_actual_lifted_pattern_cards434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m) :
    (b604ActualLiftedPattern434 r L m nu).1.card=nu.1.card ∧
      (b604ActualLiftedPattern434 r L m nu).2.card=nu.2.card := by
  simp [b604ActualLiftedPattern434]

@[simp] theorem b604_actual_freed_slots_big434
    (r : ℕ) (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (g : sourceNativeOriginalBigType434 r L) :
    sourceOriginalProbeFreedSlots434 J m hmJ (b604ActualLiftedPattern434 r L m nu)
      (sourceNativeOriginalBigToAll434 r L g) = sourceOriginalProbeFreedSlots434 J m hmJ nu g := by
  simp only [sourceOriginalProbeFreedSlots434,b604ActualLiftedPattern434,
    b604_actual_probe_lift_mem434]

@[simp] theorem b604_actual_free_count_big434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (g : sourceNativeOriginalBigType434 r L) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      (sourceNativeOriginalBigToAll434 r L g) = sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g := by
  simp only [sourceOriginalProbeFreeMarkCount434,b604_actual_freed_slots_big434]

private theorem lifted_probe_not_small
    (r : ℕ) (L : ℝ) (m : ℕ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (A : Finset (sourceNativeOriginalBigType434 r L × Fin m))
    (g : Unit ⊕ sourceNativeOriginalTsType434 r L hS) (i : Fin m) :
    ((sourceNativeOriginalCompleteEquiv434 r L hS hL
      (Sum.elim (fun u => Sum.inl u) (fun v => Sum.inr (Sum.inl v)) g)),i)
      ∉ A.map (b604ActualBigProbeEmbedding434 r L m) := by
  intro hm
  obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hm
  have hg := congrArg Prod.fst he
  change sourceNativeOriginalCompleteEquiv434 r L hS hL (Sum.inr (Sum.inr z.1)) =
    sourceNativeOriginalCompleteEquiv434 r L hS hL
      (Sum.elim (fun u => Sum.inl u) (fun v => Sum.inr (Sum.inl v)) g) at hg
  have hh := (sourceNativeOriginalCompleteEquiv434 r L hS hL).injective hg
  cases g <;> cases hh

@[simp] theorem b604_actual_free_count_S434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      (sourceNativeOriginalSGroup434 r L hS)=ell := by
  have ha (i : Fin m) := lifted_probe_not_small r L m hS hL nu.1 (Sum.inl ()) i
  have hb (i : Fin m) := lifted_probe_not_small r L m hS hL nu.2 (Sum.inl ()) i
  change ∀i,(sourceNativeOriginalSGroup434 r L hS,i)∉nu.1.map (b604ActualBigProbeEmbedding434 r L m) at ha
  change ∀i,(sourceNativeOriginalSGroup434 r L hS,i)∉nu.2.map (b604ActualBigProbeEmbedding434 r L m) at hb
  simp [sourceOriginalProbeFreeMarkCount434,sourceOriginalProbeFreedSlots434,
    b604ActualLiftedPattern434,ha,hb]

@[simp] theorem b604_actual_free_count_Ts434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (g : sourceNativeOriginalTsType434 r L hS) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      (sourceNativeOriginalTsGroup434 r L hS g)=ell := by
  have ha (i : Fin m) := lifted_probe_not_small r L m hS hL nu.1 (Sum.inr g) i
  have hb (i : Fin m) := lifted_probe_not_small r L m hS hL nu.2 (Sum.inr g) i
  change ∀i,(sourceNativeOriginalTsGroup434 r L hS g,i)∉nu.1.map (b604ActualBigProbeEmbedding434 r L m) at ha
  change ∀i,(sourceNativeOriginalTsGroup434 r L hS g,i)∉nu.2.map (b604ActualBigProbeEmbedding434 r L m) at hb
  simp [sourceOriginalProbeFreeMarkCount434,sourceOriginalProbeFreedSlots434,
    b604ActualLiftedPattern434,ha,hb]

/-- Apply the existing complete-family equivalence to the actual lifted
pattern counts: base SMALL counts and original BIG free counts agree. -/
theorem b604_actual_complete_free_count434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m) :
    (fun g => sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      (sourceNativeOriginalCompleteEquiv434 r L hS hL g)) =
    Sum.elim (fun _ : Unit => ell) (Sum.elim (fun _ => ell)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)) := by
  funext g
  rcases g with u | i | j
  · cases u
    exact b604_actual_free_count_S434 r L hS hL J ell m hmJ nu
  · exact b604_actual_free_count_Ts434 r L hS hL J ell m hmJ nu i
  · exact b604_actual_free_count_big434 r L J ell m hmJ nu j

/-- The original B578 projector is exactly the all-P projector on the
lifted pattern. This application uses the actual union and exact cards. -/
theorem b604_actual_projector_lift434
    (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m) (n : ℕ) :
    sourceB578ActualPatternProjector434 L m nu n =
      b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) n := by
  unfold sourceB578ActualPatternProjector434 b598ActualAllPPatternProjector434
    b598ActualAllPPatternPhase434 sourceNativeOriginalG434
  simp only [b604ActualLiftedPattern434,Finset.card_map]
  push_cast
  ring
end Green64Analytic.SourceBlockSieve

end

end

