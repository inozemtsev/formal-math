module

public import Green64.Library.Correlation.Part021

@[expose] public section

/-!
# Weights / IntegerNativeRow

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## IntegerNativeRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

private theorem constant_kernel (M : ℕ) (q : ℝ) (V : SG → ℝ)
    (shared : SG → Finset (Fin M)) (delta : ℤ) (K : ℂ)
    (ss st : Green64SmallHaar.GroupPermFamily (G:=SG) M)
    (x y : Green64SmallHaar.GroupState SP smallMod M) :
    Green64SmallHaar.groupPermutedKernel SP smallMod M q V shared delta
      (fun _ _ => K) ss st x y =
    if Green64SmallHaar.groupEdgeAllowedPerm SP smallMod M shared delta ss st x y then
      K*(∏ g : SG, 1/(V g:ℂ)^Green64SmallHaar.unsharedSlots M (shared g)) *
      (∏ g : SG, ((Green64SmallHaar.endpointDamping (smallMod g) M q (x g) *
        Green64SmallHaar.endpointDamping (smallMod g) M q (y g):ℝ):ℂ))
    else 0 := by
  have he : Green64SmallHaar.groupPermutedKernel SP smallMod M q V shared delta
      (fun _ _ => K) ss st x y = K*
      Green64SmallHaar.groupPermutedKernel SP smallMod M q V shared delta
        (fun _ _ => 1) ss st x y := by
    by_cases ht : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod M shared delta ss st x y
    · simp only [Green64SmallHaar.groupPermutedKernel,ite_eq_left ht,one_mul]
    · simp only [Green64SmallHaar.groupPermutedKernel,ite_eq_right ht,mul_zero]
  rw [he,memory_ind_BIG_true_kernel_V_and_endpoint_damping]
  by_cases ht : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod M shared delta ss st x y
  · simp only [ite_eq_left ht,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow]
    ac_rfl
  · simp only [ite_eq_right ht,mul_zero]

/-- The original literal integer row equals the production native row
at its actual residue states, with only the exact signed position step
imposed. This proves all SMALL/BIG kernel, damping, permutation, auxiliary
and physical Knu factors match the existing original source expression. -/
theorem b650_integer_frame_native434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta o k x y f =
    if y.val.1.val=x.val.1.val+o*k*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 f:ℤ) then
      memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns q Vsmall Vbig
        Knu zeta 0 o k x.val.2 y.val.2 f.1.1 f.1.2 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2
    else 0 := by
  by_cases hp : y.val.1.val=x.val.1.val+o*k*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 f:ℤ)
  · rw [ite_eq_left hp]
    let D := b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 f
    let U : Prop := (o=1 ∨ o = -1) ∧ k≠0 ∧
      memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns f.1.1) f.1.2 x.val.2 y.val.2
    let HB : Prop := Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
      (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) f.2.1 f.2.2.1 x.val.2.2 y.val.2.2
    let HS : Prop := Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
      (sourceSmallShared J ell) (o*k*(D:ℤ)) f.2.2.2.1 f.2.2.2.2 x.val.2.1 y.val.2.1
    let G : Prop := b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions o k x y f
    have ht := b650_integer_residue_transport434 SP smallMod BP bigMod J ell positions x y (o*k*(D:ℤ)) hp
    have hg : G ↔ U ∧ HB ∧ HS := by
      constructor
      · rintro ⟨ho,hk,ha,hsh,hp⟩
        exact ⟨⟨ho,hk,ha⟩,(fun g => ⟨ht.2 g,hsh.2 g⟩),(fun g => ⟨ht.1 g,hsh.1 g⟩)⟩
      · rintro ⟨hu,hb,hs⟩
        exact ⟨hu.1,hu.2.1,hu.2.2,⟨(fun g => (hs g).2),(fun g => (hb g).2)⟩,hp⟩
    let A : ℂ := (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ)*
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ)*
      (Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell):ℂ)
    let VB : ℂ := ∏ g : BG, 1/(Vbig g:ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
      (sourceBigShared J ell m (patterns f.1.1) g)
    let VS : ℂ := ∏ g : SG, 1/(Vsmall g:ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
      (sourceSmallShared J ell g)
    let EB : ℂ := ∏ g : BG, ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.val.2.2 g)*
      Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (y.val.2.2 g):ℝ):ℂ)
    let ES : ℂ := ∏ g : SG, ((Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (x.val.2.1 g)*
      Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (y.val.2.1 g):ℝ):ℂ)
    let C : ℂ := originalEdgeScalar
      (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
        (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (x.val.2.2 g) (f.2.1 g j))
        (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (y.val.2.2 g) (f.2.2.1 g j)))
      zeta 0 D o k
    have hb := memory_ind_BIG_true_kernel_V_and_endpoint_damping BP bigMod (J+ell) q Vbig
      (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) f.2.1 f.2.2.1 x.val.2.2 y.val.2.2
    simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow] at hb
    have hs := constant_kernel SP smallMod (J+ell) q Vsmall
      (sourceSmallShared J ell) (o*k*(D:ℤ)) C f.2.2.2.1 f.2.2.2.2 x.val.2.1 y.val.2.1
    change (if G then
      (b650NativeRealFrameWeight434 SP smallMod BP bigMod J ell m patterns q Vsmall Vbig x.val.2 y.val.2 f:ℂ)*C
      else 0) = if U then A*
      Green64SmallHaar.groupPermutedKernel BP bigMod (J+ell) q Vbig
        (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) (fun _ _ => 1) f.2.1 f.2.2.1 x.val.2.2 y.val.2.2 *
      Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
        (sourceSmallShared J ell) (o*k*(D:ℤ)) (fun _ _ => C) f.2.2.2.1 f.2.2.2.2 x.val.2.1 y.val.2.1
      else 0
    rw [hb,hs]
    change _ = if U then A*(if HB then VB*EB else 0)*(if HS then C*VS*ES else 0) else 0
    have hh : (if U then A*(if HB then VB*EB else 0)*(if HS then C*VS*ES else 0) else 0) =
        if U ∧ HB ∧ HS then A*(VB*EB)*(C*VS*ES) else 0 := by
      by_cases hu : U <;> by_cases hb : HB <;> by_cases hs : HS <;>
        simp only [hu,hb,hs,ite_true,ite_false,and_true,and_false,mul_zero,zero_mul]
    rw [hh]
    apply if_congr hg
    · dsimp [b650NativeRealFrameWeight434,A,VB,EB,VS,ES]
      push_cast
      ring
    · rfl
  · have hn : ¬ b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions o k x y f :=
      fun h => hp h.2.2.2.2
    rw [b650IntegerFrameScalar434,ite_eq_right hn,ite_eq_right hp]
end Green64FullPhysicalE

end

end

