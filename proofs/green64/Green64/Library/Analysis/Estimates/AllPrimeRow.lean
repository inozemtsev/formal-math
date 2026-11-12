module

public import Green64.Library.Correlation.Part020

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeRow

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

private theorem b643_small_constant_kernel
    (M : ℕ) (q : ℝ) (V : SG → ℝ) (shared : SG → Finset (Fin M))
    (delta : ℤ) (K : ℂ) (ss st : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (x y : Green64SmallHaar.GroupState SP smallMod M) :
    Green64SmallHaar.groupPermutedKernel SP smallMod M q V shared delta
      (fun _ _ => K) ss st x y =
    if Green64SmallHaar.groupEdgeAllowedPerm SP smallMod M shared delta ss st x y then
      K * (∏ g : SG, 1/(V g : ℂ)^Green64SmallHaar.unsharedSlots M (shared g)) *
      (∏ g : SG, ((Green64SmallHaar.endpointDamping (smallMod g) M q (x g) *
        Green64SmallHaar.endpointDamping (smallMod g) M q (y g) : ℝ) : ℂ))
    else 0 := by
  have he : Green64SmallHaar.groupPermutedKernel SP smallMod M q V shared delta
      (fun _ _ => K) ss st x y = K *
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

/-- Full original row, including zero rows, now factors with BOTH residue
transport guards. Its remaining coefficient depends only on marks/frames;
SMALL is no longer hidden inside the coefficient. -/
theorem b643_all_prime_row_weight434 {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) (i : Fin N) :
    memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta (physicalAlternatingSign i.val) k
      (states i.castSucc) (states i.succ) (frames i).1.1 (frames i).1.2
      (frames i).2.1 (frames i).2.2.1 (frames i).2.2.2.1 (frames i).2.2.2.2 =
    if b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i then
      b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
        Vsmall Vbig Knu zeta theta k
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) i *
      ((∏ g : SG, ((Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q ((states i.castSucc).1 g) *
        Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q ((states i.succ).1 g) : ℝ) : ℂ)) *
       (∏ g : BG, ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((states i.castSucc).2 g) *
        Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((states i.succ).2 g) : ℝ) : ℂ)))
    else 0 := by
  let f := frames i
  let x := states i.castSucc
  let y := states i.succ
  let o := physicalAlternatingSign i.val
  let D := memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1) f.1.2 x f.2.1 f.2.2.2.1
  let omega := b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames
  let U : Prop := (o=1 ∨ o = -1) ∧ k≠0 ∧ memoryIndependentAuxBan SP smallMod BP bigMod J ell m
    (patterns f.1.1) f.1.2 x y
  let HB : Prop := Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
    (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) f.2.1 f.2.2.1 x.2 y.2
  let HS : Prop := Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
    (sourceSmallShared J ell) (o*k*(D:ℤ)) f.2.2.2.1 f.2.2.2.2 x.1 y.1
  let T : Prop := b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i
  let G : Prop := b643AllPrimeEdgeAllowed434 SP BP J ell m patterns omega k i
  have hguard : G ∧ T ↔ U ∧ HB ∧ HS := by
    constructor
    · rintro ⟨hg,ht⟩
      exact ⟨⟨hg.1,hg.2.1,hg.2.2.1⟩,
        (fun g => ⟨ht.2 g,hg.2.2.2.1 g⟩),fun g => ⟨ht.1 g,hg.2.2.2.2 g⟩⟩
    · rintro ⟨hu,hb,hs⟩
      exact ⟨⟨hu.1,hu.2.1,hu.2.2,(fun g => (hb g).2),fun g => (hs g).2⟩,
        (fun g => (hs g).1),fun g => (hb g).1⟩
  let A : ℂ := (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ)
  let VB : ℂ := ∏ g : BG, 1/(Vbig g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
    (sourceBigShared J ell m (patterns f.1.1) g)
  let VS : ℂ := ∏ g : SG, 1/(Vsmall g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
    (sourceSmallShared J ell g)
  let EB : ℂ := ∏ g : BG, ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.2 g) *
    Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (y.2 g) : ℝ) : ℂ)
  let ES : ℂ := ∏ g : SG, ((Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (x.1 g) *
    Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (y.1 g) : ℝ) : ℂ)
  let C : ℂ := originalEdgeScalar
    (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
      (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (f.2.1 g j))
      (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (f.2.2.1 g j)))
    zeta theta D o k
  have hb := memory_ind_BIG_true_kernel_V_and_endpoint_damping BP bigMod (J+ell) q Vbig
    (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) f.2.1 f.2.2.1 x.2 y.2
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow] at hb
  have hs := b643_small_constant_kernel SP smallMod (J+ell) q Vsmall
    (sourceSmallShared J ell) (o*k*(D:ℤ)) C f.2.2.2.1 f.2.2.2.2 x.1 y.1
  change (if U then A *
      Green64SmallHaar.groupPermutedKernel BP bigMod (J+ell) q Vbig
        (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) (fun _ _ => 1) f.2.1 f.2.2.1 x.2 y.2 *
      Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
        (sourceSmallShared J ell) (o*k*(D:ℤ)) (fun _ _ => C) f.2.2.2.1 f.2.2.2.2 x.1 y.1
      else 0) = if T then (if G then A*VB*VS*C else 0)*(ES*EB) else 0
  rw [hb,hs]
  change (if U then A*(if HB then VB*EB else 0)*(if HS then C*VS*ES else 0) else 0) = _
  have hleft : (if U then A*(if HB then VB*EB else 0)*(if HS then C*VS*ES else 0) else 0) =
      if U ∧ HB ∧ HS then A*(VB*EB)*(C*VS*ES) else 0 := by
    by_cases hu : U <;> by_cases hb : HB <;> by_cases hs : HS <;> simp only [hu,hb,hs,ite_true,ite_false,and_true,and_false,mul_zero,zero_mul]
  have hright : (if T then (if G then A*VB*VS*C else 0)*(ES*EB) else 0) =
      if G ∧ T then (A*VB*VS*C)*(ES*EB) else 0 := by
    by_cases ht : T <;> by_cases hg : G <;> simp only [ht,hg,ite_true,ite_false,and_true,and_false,zero_mul]
  rw [hleft,hright]
  exact if_congr hguard.symm (by ac_rfl) rfl
end Green64FullPhysicalE

end

end

