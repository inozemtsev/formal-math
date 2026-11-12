module

public import Green64.Library.Correlation.MemoryOldFockSummedReversal
public import Green64.Library.Weights.Part002
public import Green64.Library.Correlation.Part044
public import Green64.Library.Correlation.MemoryGEDampingCancellation
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Correlation.Part008

@[expose] public section

/-!
# Correlation / Part045

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOrientedFockBalance -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Active/FRESH balance in the actual ordered frame between sigma and
tau. This uses orientedFresh; no pullback of the shared set is substituted. -/
theorem source_original_memory_ORIENTED_active_fresh_balance434
    (M : ℕ) (mu : P → ℝ) (active target : Fin M → P)
    (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (hshared : ∀ j ∈ shared,active (sigma j)=target (tau j))
    (hs : stores ⊆ orientedUnshared M shared)
    (hp : promote ⊆ orientedUnshared M shared) :
    activeMass M mu active *
      (∏ j ∈ orientedFresh M shared promote,mu (target (tau j))) *
      (∏ a : ↥promote,mu (target (tau a.val))) =
    activeMass M mu target *
      (∏ j ∈ orientedFresh M shared stores,mu (active (sigma j))) *
      (∏ a : ↥stores,mu (active (sigma a.val))) := by
  classical
  have hu : unsharedSource M shared (Equiv.refl _) = orientedUnshared M shared := by
    ext i
    have h1 : i ∈ unsharedSource M shared (Equiv.refl _) ↔ i ∉ shared := by
      unfold unsharedSource
      exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
    have h2 : i ∈ orientedUnshared M shared ↔ i ∉ shared :=
      Finset.mem_sdiff.trans (and_iff_right (Finset.mem_univ i))
    exact h1.trans h2.symm
  have hut : unsharedTarget M shared (Equiv.refl _) = orientedUnshared M shared := by
    ext i
    have h1 : i ∈ unsharedTarget M shared (Equiv.refl _) ↔ i ∉ shared := by
      unfold unsharedTarget
      exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
    have h2 : i ∈ orientedUnshared M shared ↔ i ∉ shared :=
      Finset.mem_sdiff.trans (and_iff_right (Finset.mem_univ i))
    exact h1.trans h2.symm
  have hh := physical_active_forward_reverse_mass M mu
    (fun i => active (sigma i)) (fun i => target (tau i))
    shared (Equiv.refl _) (Equiv.refl _) stores promote hshared
    (by simpa only [hu] using hs) (by simpa only [hut] using hp)
  rw [promotedTargetList_mass,storedSourceList_mass] at hh
  simp only [Equiv.refl_apply,activeMass,freshIntegration,droppedSourceMass,
    freshTargetSlots,hut,hu] at hh
  rw [Equiv.prod_comp sigma (fun i => mu (active i)),
    Equiv.prod_comp tau (fun i => mu (target i))] at hh
  have hPA : (∏ a : ↥promote,mu (target (tau a.val))) =
      ∏ i ∈ promote,mu (target (tau i)) := by
    exact Finset.prod_coe_sort promote (fun i => mu (target (tau i)))
  have hPS : (∏ a : ↥stores,mu (active (sigma a.val))) =
      ∏ i ∈ stores,mu (active (sigma i)) := by
    exact Finset.prod_coe_sort stores (fun i => mu (active (sigma i)))
  rw [hPA,hPS]
  simpa only [activeMass,orientedFresh] using hh

variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Actual active measure, actual oriented FRESH integrations, actual
OLD/Fock sum, and the original promotion normalization V^-a. The joint
test can include the true symmetric rho weights and endpoint observables. -/
def sourceOriginalMemoryOrientedPhysicalOldJoint434
    (M B j : ℕ) (hj : j ≤ B) (active target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (mu : P → ℝ) (V : ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) : ℝ :=
  activeMass M mu active *
    (∏ i ∈ orientedFresh M shared promote,mu (target (tau i))) *
    sourceOriginalMemoryPhysicalOldJoint434 modulus M B j hj
      active target sigma tau step stores promote mu F / V^promote.card

/-- Fixed-frame reversal of the full physical active/OLD joint sum.
The original unequal promotion normalizations are displayed explicitly.
This does not yet sum the remaining E labels or prove a column estimate. -/
theorem source_original_memory_ORIENTED_PHYSICAL_FOCK_summed_balance434
    (M B n : ℕ) (active target : Fin M → P)
    (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (hj : n+promote.card ≤ B) (hj' : n+stores.card ≤ B)
    (mu : P → ℝ) (hmu : ∀ p,mu p ≠ 0) (V : ℝ) (hV : V ≠ 0)
    (hshared : ∀ j ∈ shared,active (sigma j)=target (tau j))
    (hs : stores ⊆ orientedUnshared M shared)
    (hp : promote ⊆ orientedUnshared M shared)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B (n+promote.card) hj
      active target shared sigma tau step stores promote mu V F * V^promote.card =
    sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B (n+stores.card) hj'
      target active shared tau sigma (-step) promote stores mu V (fun y x => F x y) *
        V^stores.card := by
  classical
  have hOld := source_original_memory_PHYSICAL_OLD_FOCK_summed_reversal434
    modulus M B n active target sigma tau step stores promote hj hj' mu F
  have hAct := source_original_memory_ORIENTED_active_fresh_balance434
    M mu active target shared stores promote sigma tau hshared hs hp
  have hStore : (∏ a : ↥stores,mu (active (sigma a.val))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => hmu _)
  unfold sourceOriginalMemoryOrientedPhysicalOldJoint434
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hV),div_mul_cancel₀ _ (pow_ne_zero _ hV)]
  apply mul_right_cancel₀ hStore
  calc
    _ = (activeMass M mu active *
          (∏ i ∈ orientedFresh M shared promote,mu (target (tau i)))) *
        (sourceOriginalMemoryPhysicalOldJoint434 modulus M B (n+promote.card) hj
          active target sigma tau step stores promote mu F *
          (∏ a : ↥stores,mu (active (sigma a.val)))) := by ring
    _ = (activeMass M mu active *
          (∏ i ∈ orientedFresh M shared promote,mu (target (tau i))) *
          (∏ a : ↥promote,mu (target (tau a.val)))) *
        sourceOriginalMemoryPhysicalOldJoint434 modulus M B (n+stores.card) hj'
          target active tau sigma (-step) promote stores mu (fun y x => F x y) := by
      rw [hOld]
      ring
    _ = _ := by rw [hAct]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalERow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The absolute coefficient row of the literal original E restriction
to branches having at least one OLD promotion. All original choices,
legality and multiplicities remain inside this finite sum. -/
def sourceOriginalMemoryOriginalEPromotionRow434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) : ℝ :=
  ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      (∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

/-- Exact outer-sum disintegration of the original E row, without a
new kernel or a loss of equal-output or repeated-atom multiplicities. -/
theorem source_original_memory_ORIGINAL_E_promotion_row_packets434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k st =
    ∑ nu : Nu, ∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG:=BG) (J+ell),
    ∑ bt : BigGroupPerm (BG:=BG) (J+ell),
    ∑ ss : GroupPermFamily (G:=SG) (J+ell),
    ∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt q rho Vs Vb mu Knu zeta theta o k := by
  classical
  letI : Fintype (sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) := inferInstance
  letI : Fintype (GroupState SP smallMod (J+ell)) := inferInstance
  letI : Fintype (BigGroupPerm (BG:=BG) (J+ell)) := inferInstance
  letI : Fintype (GroupPermFamily (G:=SG) (J+ell)) := inferInstance
  letI (nu : Nu) : Fintype (SourceBigAux BP J m (patterns nu)) := inferInstance
  let e : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st ≃
      (Σ nu : Nu, SourceBigAux BP J m (patterns nu) ×
        BigGroupPerm (BG:=BG) (J+ell) × BigGroupPerm (BG:=BG) (J+ell) ×
        GroupPermFamily (G:=SG) (J+ell) × GroupPermFamily (G:=SG) (J+ell) ×
        sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 ×
        GroupState SP smallMod (J+ell)) :=
    { toFun := fun z => ⟨z.1,z.2.1,z.2.2.1.sigmaBig,z.2.2.1.tauBig,
        z.2.2.2.1,z.2.2.2.2,z.2.2.1.bigChoice,z.2.2.1.smallTarget⟩
      invFun := fun z => ⟨z.1,z.2.1,
        ⟨z.2.2.1,z.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2⟩,
        z.2.2.2.2.1,z.2.2.2.2.2.1⟩
      left_inv := by rintro ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩;rfl
      right_inv := by rintro ⟨nu,aux,bs,bt,ss,tt,b,zs⟩;rfl }
  unfold sourceOriginalMemoryOriginalEPromotionRow434
  rw [Fintype.sum_equiv e _ (fun z =>
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k
      (e.symm z) ∧ (∃ g : BG,(((e.symm z).2.2.1.bigChoice g).2).2.1.Nonempty)
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st (e.symm z)‖ else 0)
    (by rintro ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩; rfl)]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  rfl

/-- The corresponding literal signed E contribution. This definition
retains the original output map and arbitrary joint output observable. -/
def sourceOriginalMemoryOriginalEPromotion434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m cap patterns st o k,
    if ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty then
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
    else 0

theorem source_original_memory_ORIGINAL_E_promotion_apply_bound434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hF : ∀ y, ‖F y‖ ≤ R) :
    ‖sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k st F‖ ≤
    sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k st * R := by
  classical
  unfold sourceOriginalMemoryOriginalEPromotion434 sourceOrientedPhysicalChoices
  rw [Finset.sum_filter]
  unfold sourceOriginalMemoryOriginalEPromotionRow434
  rw [Finset.sum_mul]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro z hz
  by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
  · by_cases hp : ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty
    · simp only [hl,hp,ite_true,and_self,norm_mul]
      exact mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _)
    · simp only [hl,hp,ite_true,ite_false,and_false,norm_zero,zero_mul,le_refl]
  · simp only [hl,ite_false,false_and,norm_zero,zero_mul,le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOuterMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem source_original_memory_aux_mass_nonneg434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (J m : ℕ) (V : G → ℝ) (hV : ∀ g,0<V g) (pat : SourcePattern G J m)
    (aux : SourceBigAux BP J m pat) :
    0 ≤ sourceAuxMass BP modulus J m V pat aux := by
  unfold sourceAuxMass
  apply Finset.prod_nonneg
  intro g hg
  apply Finset.prod_nonneg
  intro j hj
  exact div_nonneg zero_le_one (mul_nonneg (hV g).le (Nat.cast_nonneg _))

/-- Exact normalization of the original untilted auxiliary harmonic law,
including every labelled draw and repetitions. -/
theorem source_original_memory_aux_mass_sum_one434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (J m : ℕ) (V : G → ℝ) (hV : ∀ g,0<V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(modulus g p:ℝ)=V g)
    (pat : SourcePattern G J m) :
    (∑ aux : SourceBigAux BP J m pat,sourceAuxMass BP modulus J m V pat aux)=1 := by
  classical
  have hOne (g : G) : (∑ p : BP g,1/(V g*(modulus g p:ℝ)))=1 := by
    simp_rw [one_div,mul_inv_rev]
    rw [← Finset.sum_mul]
    simpa only [one_div] using congrArg (fun t => t*(V g)⁻¹) (hHarmonic g) |>.trans
      (mul_inv_cancel₀ (ne_of_gt (hV g)))
  have hLocal (g : G) :
      (∑ f : ↥(pat.free g) → BP g,∏ j : ↥(pat.free g),
        1/(V g*(modulus g (f j):ℝ)))=1 := by
    calc
      _ = ∏ j : ↥(pat.free g),∑ p : BP g,1/(V g*(modulus g p:ℝ)) := by
        convert (Fintype.prod_sum (fun (_j : ↥(pat.free g)) (p : BP g) =>
          (1:ℝ)/(V g*(modulus g p:ℝ)))).symm using 1
      _ = 1 := by simp only [hOne,Finset.prod_const_one]
  change (∑ aux : (g : G) → ↥(pat.free g) → BP g,
    ∏ g : G,∏ j : ↥(pat.free g),1/(V g*(modulus g (aux g j):ℝ)))=1
  calc
    _ = ∏ g : G,∑ f : ↥(pat.free g) → BP g,
        ∏ j : ↥(pat.free g),1/(V g*(modulus g (f j):ℝ)) := by
      convert (Fintype.prod_sum (fun (g : G) (f : ↥(pat.free g) → BP g) =>
        ∏ j : ↥(pat.free g),(1:ℝ)/(V g*(modulus g (f j):ℝ)))).symm using 1
    _ = 1 := by simp only [hLocal,Finset.prod_const_one]

/-- The literal auxiliary and both BIG permutation masses sum to one.
There is no free-label, factorial or BIG-group counting loss. -/
theorem source_original_memory_BIG_AUX_total_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (J ell m : ℕ) (V : G → ℝ) (hV : ∀ g,0<V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(modulus g p:ℝ)=V g)
    (pat : SourcePattern G J m) :
    (∑ aux : SourceBigAux BP J m pat,
      ∑ bs : BigGroupPerm (BG:=G) (J+ell),∑ bt : BigGroupPerm (BG:=G) (J+ell),
      ‖(sourceAuxMass BP modulus J m V pat aux:ℂ)*
        (bigEndpointPairMass (BG:=G) (J+ell):ℂ)‖)=1 := by
  classical
  let Pm := bigEndpointPairMass (BG:=G) (J+ell)
  let n : ℝ := Fintype.card (BigGroupPerm (BG:=G) (J+ell))
  have hPm : 0 ≤ Pm := by
    exact (groupPermutationPairMass_positive (G:=G) (J+ell)).le
  have hn : Pm*n^2=1 := by
    have hh := bigEndpointPairMass_normalized (BG:=G) (J+ell)
    dsimp only [Pm,n]
    simp only [BigGroupPerm,Fintype.card_fun,Fintype.card_perm,Fintype.card_fin] at hh ⊢
    exact_mod_cast hh
  have hNorm (aux : SourceBigAux BP J m pat) :
      ‖(sourceAuxMass BP modulus J m V pat aux:ℂ)*
        (bigEndpointPairMass (BG:=G) (J+ell):ℂ)‖ =
      sourceAuxMass BP modulus J m V pat aux*Pm := by
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (source_original_memory_aux_mass_nonneg434 BP modulus J m V hV pat aux),
      abs_of_nonneg hPm]
  simp_rw [hNorm]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  calc
    _ = ∑ aux : SourceBigAux BP J m pat,
        sourceAuxMass BP modulus J m V pat aux*(Pm*n^2) := by
      apply Finset.sum_congr rfl
      intro a ha
      change n*(n*(_*Pm))=_*(Pm*n^2)
      ring
    _ = ∑ aux : SourceBigAux BP J m pat,sourceAuxMass BP modulus J m V pat aux := by
      simp only [hn,mul_one]
    _ = 1 := source_original_memory_aux_mass_sum_one434 BP modulus J m V hV hHarmonic pat
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalEOuter -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact assembly of every outer original E sum. This is the finite
transfer lemma; the physical theorem below supplies its rare-row input
and the actual canonical cap, rather than assuming their smallness. -/
theorem source_original_memory_ORIGINAL_E_promotion_outer_bound434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
    (J ell m : ℕ) (cap : BG → ℕ)
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bigMod g p:ℝ)=Vb g)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖Knu nu aux s t‖ ≤ Kcap nu)
    (R : ℝ)
    (hRare : ∀ nu (aux : SourceBigAux BP J m (patterns nu))
      (bs bt : BigGroupPerm (BG:=BG) (J+ell)),
      ((∑ ss : GroupPermFamily (G:=SG) (J+ell),
        sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod BP bigMod
          J ell m cap (patterns nu) aux st bs bt ss mu Vb rho o k) /
        (((J+ell).factorial:ℝ)^(Fintype.card SG))) ≤ R) :
    sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k st ≤
      (∑ nu : Nu,Kcap nu)*(∏ g : SG,memorySmallRowConstant q (Vs g) ell)*R := by
  classical
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  have hsqrt : Real.sqrt q < 1 := by
    nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
  have hCs : 0 ≤ Cs := by
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    have hs : 0<1-Real.sqrt q := sub_pos.mpr hsqrt
    dsimp only [memorySmallRowConstant]
    positivity
  rw [source_original_memory_ORIGINAL_E_promotion_row_packets434]
  have hNu (nu : Nu) :
      (∑ aux : SourceBigAux BP J m (patterns nu),
        ∑ bs : BigGroupPerm (BG:=BG) (J+ell),
        ∑ bt : BigGroupPerm (BG:=BG) (J+ell),
        ∑ ss : GroupPermFamily (G:=SG) (J+ell),
        ∑ tt : GroupPermFamily (G:=SG) (J+ell),
        sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod BP bigMod
          J ell m cap patterns nu aux st bs bt ss tt q rho Vs Vb mu Knu zeta theta o k) ≤
      Kcap nu*Cs*R := by
    let W := fun aux : SourceBigAux BP J m (patterns nu) =>
      ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ)*
        (bigEndpointPairMass (BG:=BG) (J+ell):ℂ)‖
    calc
      _ ≤ ∑ aux : SourceBigAux BP J m (patterns nu),
          ∑ bs : BigGroupPerm (BG:=BG) (J+ell),
          ∑ bt : BigGroupPerm (BG:=BG) (J+ell),
          W aux*(Kcap nu*Cs*R) := by
        apply Finset.sum_le_sum
        intro aux ha
        apply Finset.sum_le_sum
        intro bs hb
        apply Finset.sum_le_sum
        intro bt hc
        have hp := source_original_memory_ORIGINAL_packet_SMALL_average434
          SP smallMod BP bigMod J ell m cap patterns nu aux st bs bt
          q rho Vs Vb hq hq1 hVs mu Knu zeta theta o k ho (Kcap nu)
          (fun t => hK nu aux _ t)
        have hw : 0 ≤ W aux := norm_nonneg _
        have hh := mul_le_mul_of_nonneg_left (hRare nu aux bs bt)
          (mul_nonneg (mul_nonneg hw (hK0 nu)) hCs)
        exact hp.trans (by convert hh using 1 <;> dsimp only [W,Cs] <;> ring)
      _ = (∑ aux : SourceBigAux BP J m (patterns nu),
          ∑ bs : BigGroupPerm (BG:=BG) (J+ell),
          ∑ bt : BigGroupPerm (BG:=BG) (J+ell),W aux)*(Kcap nu*Cs*R) := by
        simp only [Finset.sum_mul]
      _ = Kcap nu*Cs*R := by
        rw [source_original_memory_BIG_AUX_total_mass434 BP bigMod J ell m Vb hVb
          hHarmonic (patterns nu),one_mul]
  calc
    _ ≤ ∑ nu : Nu,Kcap nu*Cs*R := Finset.sum_le_sum (fun nu _ => hNu nu)
    _ = _ := by simp only [Finset.sum_mul];rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalFockSectors -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The actual source and output capacity conditions for a frame with
a promotions and b stores. -/
abbrev SourceOriginalMemoryAdmissibleSector434 (B a b : ℕ) :=
  {j : Fin (B+1) // a ≤ j.val ∧ j.val-a+b ≤ B}

/-- Swap source/output sizes while preserving the number of survivors. -/
def sourceOriginalMemorySectorReverse434 (B a b : ℕ) :
    SourceOriginalMemoryAdmissibleSector434 B a b ≃
      SourceOriginalMemoryAdmissibleSector434 B b a where
  toFun j := ⟨⟨j.val.val-a+b,by have := j.property;omega⟩,by
    have := j.property;have := j.val.isLt;dsimp;omega⟩
  invFun j := ⟨⟨j.val.val-b+a,by have := j.property;omega⟩,by
    have := j.property;have := j.val.isLt;dsimp;omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have := j.property
    dsimp
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have := j.property
    dsimp
    omega

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- The scalar capacity condition is exactly the length of the literal
ordered physical output, for every actual OLD injection. -/
theorem source_original_memory_PHYSICAL_OLD_sector_cutoff434
    (M B j : ℕ) (hj : j ≤ B) (active : Fin M → P)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M))
    (old : Fin j → Green64Fock.Atom P modulus) (f : ↥promote ↪ Fin j) :
    (physicalPendingOutput modulus M B
      (active,⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩) sigma step ⟨stores,promote,f⟩).length ≤ B ↔
      promote.card ≤ j ∧ j-promote.card+stores.card ≤ B := by
  have ha : promote.card ≤ j := by
    simpa using Fintype.card_le_of_injective f f.injective
  rw [pending_output_length]
  simpa only [ha,true_and]

/-- All source OLD sectors allowed by the original capacity before and
after the actual transition. All ordered tuples and injections are
still summed with the original 1/j! inside each summand. -/
def sourceOriginalMemoryOrientedPhysicalFockJoint434
    (M B : ℕ) (active target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (mu : P → ℝ) (V : ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) : ℝ :=
  ∑ j : SourceOriginalMemoryAdmissibleSector434 B promote.card stores.card,
    sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B j.val.val
      (Nat.lt_succ_iff.mp j.val.isLt) active target shared sigma tau step
      stores promote mu V F

/-- Exact full finite OLD-sector balance, still at a fixed active,
pattern, endpoint-permutation and store/promotion frame. -/
theorem source_original_memory_PHYSICAL_OLD_FOCK_all_sectors_balance434
    (M B : ℕ) (active target : Fin M → P)
    (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (mu : P → ℝ) (hmu : ∀ p,mu p ≠ 0) (V : ℝ) (hV : V ≠ 0)
    (hshared : ∀ j ∈ shared,active (sigma j)=target (tau j))
    (hs : stores ⊆ orientedUnshared M shared)
    (hp : promote ⊆ orientedUnshared M shared)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryOrientedPhysicalFockJoint434 modulus M B
      active target shared sigma tau step stores promote mu V F * V^promote.card =
    sourceOriginalMemoryOrientedPhysicalFockJoint434 modulus M B
      target active shared tau sigma (-step) promote stores mu V (fun y x => F x y) *
        V^stores.card := by
  classical
  unfold sourceOriginalMemoryOrientedPhysicalFockJoint434
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Fintype.sum_equiv (sourceOriginalMemorySectorReverse434 B promote.card stores.card)
  intro j
  have hj : j.val.val-promote.card+promote.card ≤ B := by
    have := j.property;have := j.val.isLt;omega
  have hh := source_original_memory_ORIENTED_PHYSICAL_FOCK_summed_balance434
    modulus M B (j.val.val-promote.card) active target shared stores promote sigma tau step
    hj j.property.2 mu hmu V hV hshared hs hp F
  simpa only [Nat.sub_add_cancel j.property.1,sourceOriginalMemorySectorReverse434,
    Equiv.coe_fn_mk] using hh

/-- Expanded sum over all original sector indices; excluded source or
output sectors have zero contribution. -/
theorem source_original_memory_PHYSICAL_FOCK_sector_sum_expansion434
    (M B : ℕ) (active target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (mu : P → ℝ) (V : ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryOrientedPhysicalFockJoint434 modulus M B
      active target shared sigma tau step stores promote mu V F =
    ∑ j : Fin (B+1),
      if promote.card ≤ j.val ∧ j.val-promote.card+stores.card ≤ B then
        sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B j.val
          (Nat.lt_succ_iff.mp j.isLt) active target shared sigma tau step stores promote mu V F
      else 0 := by
  classical
  unfold sourceOriginalMemoryOrientedPhysicalFockJoint434
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
  intro j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFockSectorDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- The auxiliary density V^j absorbs the exact original V^-a/V^-b
promotion ratio. No upper bound on V is used in this equality. -/
theorem source_original_memory_PHYSICAL_FOCK_sector_density_balance434
    (M B n : ℕ) (active target : Fin M → P)
    (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (hj : n+promote.card ≤ B) (hj' : n+stores.card ≤ B)
    (mu : P → ℝ) (hmu : ∀ p,mu p ≠ 0) (V : ℝ) (hV : V ≠ 0)
    (hshared : ∀ j ∈ shared,active (sigma j)=target (tau j))
    (hs : stores ⊆ orientedUnshared M shared)
    (hp : promote ⊆ orientedUnshared M shared)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B (n+promote.card) hj
      active target shared sigma tau step stores promote mu V F * V^(n+promote.card) =
    sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B (n+stores.card) hj'
      target active shared tau sigma (-step) promote stores mu V (fun y x => F x y) *
        V^(n+stores.card) := by
  have hh := source_original_memory_ORIENTED_PHYSICAL_FOCK_summed_balance434
    modulus M B n active target shared stores promote sigma tau step hj hj'
    mu hmu V hV hshared hs hp F
  calc
    _ = (sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B (n+promote.card) hj
      active target shared sigma tau step stores promote mu V F * V^promote.card)*V^n := by
        rw [pow_add];ring
    _ = _ := by rw [hh,pow_add];ring

def sourceOriginalMemoryDensityWeightedFockJoint434
    (M B : ℕ) (active target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (mu : P → ℝ) (V : ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) : ℝ :=
  ∑ j : SourceOriginalMemoryAdmissibleSector434 B promote.card stores.card,
    sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B j.val.val
      (Nat.lt_succ_iff.mp j.val.isLt) active target shared sigma tau step
      stores promote mu V F * V^j.val.val

/-- Full original finite OLD-sector reversal with the auxiliary V^j
density. Remaining E labels and G/birth norms are not asserted here. -/
theorem source_original_memory_PHYSICAL_FOCK_density_all_sectors434
    (M B : ℕ) (active target : Fin M → P)
    (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (mu : P → ℝ) (hmu : ∀ p,mu p ≠ 0) (V : ℝ) (hV : V ≠ 0)
    (hshared : ∀ j ∈ shared,active (sigma j)=target (tau j))
    (hs : stores ⊆ orientedUnshared M shared)
    (hp : promote ⊆ orientedUnshared M shared)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryDensityWeightedFockJoint434 modulus M B
      active target shared sigma tau step stores promote mu V F =
    sourceOriginalMemoryDensityWeightedFockJoint434 modulus M B
      target active shared tau sigma (-step) promote stores mu V (fun y x => F x y) := by
  classical
  unfold sourceOriginalMemoryDensityWeightedFockJoint434
  apply Fintype.sum_equiv (sourceOriginalMemorySectorReverse434 B promote.card stores.card)
  intro j
  have hj : j.val.val-promote.card+promote.card ≤ B := by
    have := j.property;have := j.val.isLt;omega
  have hh := source_original_memory_PHYSICAL_FOCK_sector_density_balance434
    modulus M B (j.val.val-promote.card) active target shared stores promote sigma tau step
    hj j.property.2 mu hmu V hV hshared hs hp F
  simpa only [Nat.sub_add_cancel j.property.1,sourceOriginalMemorySectorReverse434,
    Equiv.coe_fn_mk] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryLegalFockDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- The OLD-independent portion of the literal oriented BIG legality.
Both nondivisibility conditions are on the actual ordered endpoints. -/
def sourceOriginalMemoryFixedBigLegal434
    (M : ℕ) (active target : Fin M → P) (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) : Prop :=
  (∀ i ∈ shared,active (sigma i)=target (tau i)) ∧
  stores ⊆ orientedUnshared M shared ∧ promote ⊆ orientedUnshared M shared ∧
  (∀ i ∈ promote,¬ modulus (target (tau i)) ∣ D) ∧
  (∀ i ∈ stores,¬ modulus (active (sigma i)) ∣ D)

/-- Complete physical legality separates into the actual fixed frame,
the two OLD tests and the exact source/output sector constraints. -/
theorem source_original_memory_BIG_legal_disintegration434
    (M B : ℕ) (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c ↔
      sourceOriginalMemoryFixedBigLegal434 modulus M x.1 target shared c.1 c.2.1 sigma tau D ∧
      (∀ a : ↥c.2.1,target (tau a.val)=(x.2.2 (c.2.2 a)).1) ∧
      (∀ a : ↥c.2.1,(x.2.2 (c.2.2 a)).2+
        (step:ZMod (modulus (x.2.2 (c.2.2 a)).1))=0) ∧
      c.2.1.card ≤ x.2.1.val ∧ x.2.1.val-c.2.1.card+c.1.card ≤ B := by
  have ha : c.2.1.card ≤ x.2.1.val := by
    simpa using Fintype.card_le_of_injective c.2.2 c.2.2.injective
  constructor
  · intro h
    refine ⟨⟨h.shared_copy,h.stores_unshared,h.promotes_unshared,?_,h.stored_not_dividing⟩,
      h.promoted_matches,h.promoted_zero,ha,?_⟩
    · intro i hi
      rw [h.promoted_matches ⟨i,hi⟩]
      exact h.promoted_not_dividing ⟨i,hi⟩
    · simpa only [pending_output_length] using h.output_within_cutoff
  · rintro ⟨hfix,hm,hz,ha,hcut⟩
    refine ⟨hfix.1,hfix.2.1,hfix.2.2.1,hm,hz,?_,hfix.2.2.2.2,?_⟩
    · intro a
      rw [← hm a]
      exact hfix.2.2.2.1 a.val a.property
    · simpa only [pending_output_length] using hcut

theorem source_original_memory_BIG_fixed_legal_reverse434
    (M : ℕ) (active target : Fin M → P) (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) :
    sourceOriginalMemoryFixedBigLegal434 modulus M active target shared stores promote sigma tau D ↔
    sourceOriginalMemoryFixedBigLegal434 modulus M target active shared promote stores tau sigma D := by
  unfold sourceOriginalMemoryFixedBigLegal434
  constructor <;> rintro ⟨hc,hs,hp,ha,hb⟩
  · exact ⟨fun i hi => (hc i hi).symm,hp,hs,hb,ha⟩
  · exact ⟨fun i hi => (hc i hi).symm,hp,hs,hb,ha⟩

/-- The actual BIG branch norm expressed on its two physical multisets.
The OLD and output rho factors both remain present. -/
theorem source_original_memory_BIG_norm_multisets434
    (M B : ℕ) (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho : ℝ)
    (hV : 0<V) (hr : 0 ≤ rho) (x : BigState modulus M B)
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    ‖orientedBigBranchCoefficient modulus M B mu V rho x target shared sigma tau step c‖ =
    (rho^((Green64Fock.fockMultiset x.2).countP (fun z => z.2=0)+
      (physicalPendingMultiset modulus M B x sigma step c).countP (fun z => z.2=0)) /
      V^c.2.1.card) * ∏ i ∈ orientedFresh M shared c.2.1,mu (target (tau i)) := by
  have hOld : (Green64Fock.fockMultiset x.2).countP (fun z => z.2=0)=oldZeroCount x.2 := by
    rw [Green64Fock.fockMultiset,Multiset.coe_countP]
    exact Green64MemoryGhostOp.source_original_GHOST_Fock_list_count434 x.2
  have hOut : (physicalPendingMultiset modulus M B x sigma step c).countP (fun z => z.2=0) =
      outputZeroCount modulus M B x sigma step c := by
    rw [physicalPendingMultiset,Multiset.coe_countP];rfl
  have hAbs (p : P) : |mu p|=mu p := abs_of_nonneg (hmu p)
  rw [hOld,hOut]
  simp only [orientedBigBranchCoefficient,norm_mul,norm_pow,norm_div,norm_one,norm_prod,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_pos hV,hAbs]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryLegalFockReversal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- The full literal fixed-frame BIG joint: every original OLD sector,
ordered atom tuple and injection, the original active/Fock measure,
actual branch legality and norm, and the auxiliary density V^j. -/
def sourceOriginalMemoryLegalFockDensityJoint434
    (M B : ℕ) (active target : Fin M → P)
    (shared stores promote : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (mu : P → ℝ) (V rho : ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) : ℝ :=
  ∑ j : Fin (B+1), ∑ old : Fin j.val → Green64Fock.Atom P modulus,
    ∑ f : ↥promote ↪ Fin j.val,
    let x : BigState modulus M B := (active,⟨j,old⟩)
    activeMass M mu active * Green64Fock.fockMass
      (fun z : Green64Fock.Atom P modulus => mu z.1) x.2 * V^j.val *
      (if OrientedBigEdgeLegal modulus M B x target shared sigma tau D step ⟨stores,promote,f⟩
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x target shared
        sigma tau step ⟨stores,promote,f⟩‖ *
        F (Green64Fock.fockMultiset x.2)
          (physicalPendingMultiset modulus M B x sigma step ⟨stores,promote,f⟩)
      else 0)

theorem source_original_memory_DENSITY_FOCK_sector_expansion434
    (M B : ℕ) (active target : Fin M → P) (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ) (mu : P → ℝ) (V : ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryDensityWeightedFockJoint434 modulus M B active target shared
      sigma tau step stores promote mu V F =
    ∑ j : Fin (B+1),
      if promote.card ≤ j.val ∧ j.val-promote.card+stores.card ≤ B then
        sourceOriginalMemoryOrientedPhysicalOldJoint434 modulus M B j.val
          (Nat.lt_succ_iff.mp j.isLt) active target shared sigma tau step
          stores promote mu V F * V^j.val
      else 0 := by
  classical
  unfold sourceOriginalMemoryDensityWeightedFockJoint434
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
  intro j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

/-- Exact connection to the original legal branch sum. In particular
neither p∤D, the capacity tests, nor either endpoint rho factor is dropped. -/
theorem source_original_memory_LEGAL_FOCK_density_factor434
    (M B : ℕ) (active target : Fin M → P) (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho : ℝ) (hV : 0<V) (hr : 0 ≤ rho)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryLegalFockDensityJoint434 modulus M B active target shared stores promote
      sigma tau D step mu V rho F =
    if sourceOriginalMemoryFixedBigLegal434 modulus M active target shared stores promote sigma tau D
    then sourceOriginalMemoryDensityWeightedFockJoint434 modulus M B active target shared sigma tau step
      stores promote mu V (fun X Y =>
        rho^(X.countP (fun z => z.2=0)+Y.countP (fun z => z.2=0))*F X Y)
    else 0 := by
  classical
  unfold sourceOriginalMemoryLegalFockDensityJoint434
  dsimp only
  by_cases hfix : sourceOriginalMemoryFixedBigLegal434 modulus M active target
      shared stores promote sigma tau D
  · rw [if_pos hfix,source_original_memory_DENSITY_FOCK_sector_expansion434]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hc : promote.card ≤ j.val ∧ j.val-promote.card+stores.card ≤ B
    · rw [if_pos hc]
      unfold sourceOriginalMemoryOrientedPhysicalOldJoint434 sourceOriginalMemoryPhysicalOldJoint434
      simp only [div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro old hold
      apply Finset.sum_congr rfl
      intro f hf
      let x : BigState modulus M B := (active,⟨j,old⟩)
      have he := source_original_memory_BIG_legal_disintegration434 modulus M B x target shared
        sigma tau D step ⟨stores,promote,f⟩
      by_cases ht : (∀ a : ↥promote,target (tau a.val)=(old (f a)).1) ∧
        (∀ a : ↥promote,(old (f a)).2+(step:ZMod (modulus (old (f a)).1))=0)
      · have hl : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
            ⟨stores,promote,f⟩ := he.mpr ⟨hfix,ht.1,ht.2,hc⟩
        rw [if_pos hl,if_pos ht,source_original_memory_BIG_norm_multisets434 modulus M B
          mu hmu V rho hV hr]
        dsimp only [x]
        simp only [div_eq_mul_inv]
        ring
      · have hl : ¬ OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
            ⟨stores,promote,f⟩ := fun h => ht ⟨(he.mp h).2.1,(he.mp h).2.2.1⟩
        rw [if_neg hl,if_neg ht]
        ring
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro old hold
      apply Finset.sum_eq_zero
      intro f hf
      have hn : ¬ OrientedBigEdgeLegal modulus M B (active,⟨j,old⟩) target shared
          sigma tau D step ⟨stores,promote,f⟩ := by
        intro h
        have hh := (source_original_memory_BIG_legal_disintegration434 modulus M B
          (active,⟨j,old⟩) target shared sigma tau D step ⟨stores,promote,f⟩).mp h
        exact hc hh.2.2.2
      rw [if_neg hn,mul_zero]
  · rw [if_neg hfix]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro old hold
    apply Finset.sum_eq_zero
    intro f hf
    have hn : ¬ OrientedBigEdgeLegal modulus M B (active,⟨j,old⟩) target shared
        sigma tau D step ⟨stores,promote,f⟩ := by
      intro h
      exact hfix ((source_original_memory_BIG_legal_disintegration434 modulus M B
        (active,⟨j,old⟩) target shared sigma tau D step ⟨stores,promote,f⟩).mp h).1
    rw [if_neg hn,mul_zero]

/-- Full fixed-frame physical detailed balance, now for the literal legal
branch norm with all OLD sectors summed. No symmetry premise on F is used. -/
theorem source_original_memory_LEGAL_FOCK_density_reverse434
    (M B : ℕ) (active target : Fin M → P) (shared stores promote : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (mu : P → ℝ) (hmu : ∀ p,0 < mu p) (V rho : ℝ) (hV : 0<V) (hr : 0 ≤ rho)
    (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryLegalFockDensityJoint434 modulus M B active target shared stores promote
      sigma tau D step mu V rho F =
    sourceOriginalMemoryLegalFockDensityJoint434 modulus M B target active shared promote stores
      tau sigma D (-step) mu V rho (fun Y X => F X Y) := by
  rw [source_original_memory_LEGAL_FOCK_density_factor434 modulus M B active target shared
    stores promote sigma tau D step mu (fun p => (hmu p).le) V rho hV hr,
    source_original_memory_LEGAL_FOCK_density_factor434 modulus M B target active shared
    promote stores tau sigma D (-step) mu (fun p => (hmu p).le) V rho hV hr]
  rw [← source_original_memory_BIG_fixed_legal_reverse434 modulus M active target shared
    stores promote sigma tau D]
  split_ifs with hfix
  · rw [source_original_memory_PHYSICAL_FOCK_density_all_sectors434 modulus M B
      active target shared stores promote sigma tau step mu (fun p => ne_of_gt (hmu p))
      V (ne_of_gt hV) hfix.1 hfix.2.1 hfix.2.2.1]
    congr 1
    funext X Y
    rw [Nat.add_comm]
  · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBigDensityColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (M B : ℕ)

def sourceOriginalMemoryBigDensityMass434 (mu : P → ℝ) (V : ℝ)
    (x : BigState modulus M B) : ℝ :=
  bigStateMass modulus M B mu x * V^x.2.1.val

def sourceOriginalMemoryBigProjection434 (x : BigState modulus M B) :
    BigPhysicalOutput modulus M := (x.1,Green64Fock.fockMultiset x.2)

/-- Literal complete BIG branch pairing against an arbitrary JOINT
observable of the two physical outputs. Every original branch, target
and Fock source is summed; only the auxiliary Hilbert density is added. -/
def sourceOriginalMemoryBigDensityBilinear434
    (mu : P → ℝ) (V rho : ℝ) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → BigPhysicalOutput modulus M → ℝ) : ℝ :=
  ∑ x : BigState modulus M B,
    sourceOriginalMemoryBigDensityMass434 modulus M B mu V x *
    ∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖ *
        F (sourceOriginalMemoryBigProjection434 modulus M B x)
          (t,physicalPendingMultiset modulus M B x sigma step c)
      else 0

/-- Exact disintegration of the complete source pairing into the legal
Fock frames. Ordered multiplicity is kept even for repeated atoms. -/
theorem source_original_memory_BIG_density_bilinear_disintegration434
    (mu : P → ℝ) (V rho : ℝ) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → BigPhysicalOutput modulus M → ℝ) :
    sourceOriginalMemoryBigDensityBilinear434 modulus M B mu V rho shared sigma tau D step F =
    ∑ a : Fin M → P,∑ t : Fin M → P,∑ S : Finset (Fin M),∑ A : Finset (Fin M),
      sourceOriginalMemoryLegalFockDensityJoint434 modulus M B a t shared S A
        sigma tau D step mu V rho (fun X Y => F (a,X) (t,Y)) := by
  classical
  letI (A : Finset (Fin M)) (j : Fin (B+1)) : Fintype
      ((Fin j.val → Green64Fock.Atom P modulus) × (↥A ↪ Fin j.val)) := inferInstance
  letI (A : Finset (Fin M)) : Fintype
      (Σ j : Fin (B+1),(Fin j.val → Green64Fock.Atom P modulus) × (↥A ↪ Fin j.val)) := inferInstance
  letI : Fintype (Σ A : Finset (Fin M),Σ j : Fin (B+1),
      (Fin j.val → Green64Fock.Atom P modulus) × (↥A ↪ Fin j.val)) := inferInstance
  let e :
      (Σ x : BigState modulus M B,BigEdgeChoice modulus M B x × (Fin M → P)) ≃
      (Σ a : Fin M → P,(Fin M → P) ×
        (Σ S : Finset (Fin M),Σ A : Finset (Fin M),Σ j : Fin (B+1),
          (Fin j.val → Green64Fock.Atom P modulus) × (↥A ↪ Fin j.val))) :=
    { toFun := fun z => ⟨z.1.1,z.2.2,z.2.1.1,z.2.1.2.1,z.1.2.1,z.1.2.2,z.2.1.2.2⟩
      invFun := fun z => ⟨(z.1,⟨z.2.2.2.2.1,z.2.2.2.2.2.1⟩),
        (z.2.2.1,⟨z.2.2.2.1,z.2.2.2.2.2.2⟩),z.2.1⟩
      left_inv := by rintro ⟨⟨a,j,old⟩,⟨S,A,f⟩,t⟩;rfl
      right_inv := by rintro ⟨a,t,S,A,j,old,f⟩;rfl }
  let w := fun (z : Σ x : BigState modulus M B,
      BigEdgeChoice modulus M B x × (Fin M → P)) =>
    sourceOriginalMemoryBigDensityMass434 modulus M B mu V z.1 *
      (if OrientedBigEdgeLegal modulus M B z.1 z.2.2 shared sigma tau D step z.2.1
      then ‖orientedBigBranchCoefficient modulus M B mu V rho z.1 z.2.2
        shared sigma tau step z.2.1‖ *
        F (sourceOriginalMemoryBigProjection434 modulus M B z.1)
          (z.2.2,physicalPendingMultiset modulus M B z.1 sigma step z.2.1)
      else 0)
  have he := Fintype.sum_equiv e w (fun z => w (e.symm z))
    (by intro z;rw [e.symm_apply_apply])
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,
    sourceOriginalMemoryBigDensityBilinear434,sourceOriginalMemoryLegalFockDensityJoint434,
    sourceOriginalMemoryBigDensityMass434,sourceOriginalMemoryBigProjection434,
    bigStateMass,Green64Fock.sourceAtomMu,Green64Fock.lambdaMass,Finset.mul_sum,w,e,Equiv.symm_apply_apply,
    Equiv.coe_fn_symm_mk] at he ⊢
  convert he using 1 <;> congr <;> exact Subsingleton.elim _ _

/-- Complete BIG weighted detailed balance. Unlike a fixed-sector
integrand identity, this includes all physical states and all original
store/promotion choices and tests. The joint observable is arbitrary. -/
theorem source_original_memory_BIG_density_bilinear_reverse434
    (mu : P → ℝ) (hmu : ∀ p,0 < mu p) (V rho : ℝ) (hV : 0<V) (hr : 0 ≤ rho)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → BigPhysicalOutput modulus M → ℝ) :
    sourceOriginalMemoryBigDensityBilinear434 modulus M B mu V rho shared sigma tau D step F =
    sourceOriginalMemoryBigDensityBilinear434 modulus M B mu V rho shared tau sigma D (-step)
      (fun Y X => F X Y) := by
  rw [source_original_memory_BIG_density_bilinear_disintegration434,
    source_original_memory_BIG_density_bilinear_disintegration434]
  conv_lhs =>
    arg 2;ext a
    arg 2;ext t
    arg 2;ext S
    arg 2;ext A
    rw [source_original_memory_LEGAL_FOCK_density_reverse434 modulus M B a t shared S A
      sigma tau D step mu hmu V rho hV hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

/-- The auxiliary orbit mass uses the genuine ordered-fibre sum, not
an assumed cancellation of factorial or repeated-atom multiplicities. -/
def sourceOriginalMemoryBigDensityOrbitMass434
    (mu : P → ℝ) (V : ℝ) (y : BigPhysicalOutput modulus M) : ℝ :=
  ∑ x : BigState modulus M B,
    if sourceOriginalMemoryBigProjection434 modulus M B x=y
    then sourceOriginalMemoryBigDensityMass434 modulus M B mu V x else 0

/-- Actual complete weighted BIG column, at the physical Fock orbit.
The constant is independent of OLD length, cutoff, and number of shared
slots. This is a proved bound, not an assumed column/Schur hypothesis. -/
theorem source_original_memory_BIG_density_column434
    (mu : P → ℝ) (hmu : ∀ p,0 < mu p) (V rho R : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1)
    (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d)
    (y : BigPhysicalOutput modulus M) :
    sourceOriginalMemoryBigDensityBilinear434 modulus M B mu V rho shared sigma tau D step
      (fun _ Y => if Y=y then 1 else 0) ≤
    ((4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 V⁻¹)^d*R^d))) *
      sourceOriginalMemoryBigDensityOrbitMass434 modulus M B mu V y := by
  rw [source_original_memory_BIG_density_bilinear_reverse434 modulus M B mu hmu V rho
    hV hr.le]
  unfold sourceOriginalMemoryBigDensityBilinear434 sourceOriginalMemoryBigDensityOrbitMass434
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  have hm : 0 ≤ sourceOriginalMemoryBigDensityMass434 modulus M B mu V x :=
    mul_nonneg (bigStateMass_positive modulus M B mu hmu x).le (pow_nonneg hV.le _)
  by_cases hy : sourceOriginalMemoryBigProjection434 modulus M B x=y
  · simp only [hy,ite_true,mul_one]
    have hrow := source_original_memory_BIG_complete_absolute_row434 modulus M B mu
      (fun p => (hmu p).le) V rho R hV hr hr1 hR hMass x shared tau sigma D (-step) d hd
    exact (mul_le_mul_of_nonneg_left hrow hm).trans_eq (mul_comm _ _)
  · simp only [hy,ite_false,mul_zero,ite_self,Finset.sum_const_zero,le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBigDensityPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- The literal two-ended weighted BIG kernel on physical Fock orbits. -/
def sourceOriginalMemoryBigDensityPair434
    (mu : P → ℝ) (V rho : ℝ) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (X Y : BigPhysicalOutput modulus M) : ℝ :=
  ∑ x : BigState modulus M B,
    sourceOriginalMemoryBigDensityMass434 modulus M B mu V x *
    ∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if sourceOriginalMemoryBigProjection434 modulus M B x=X ∧
        OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
        (t,physicalPendingMultiset modulus M B x sigma step c)=Y
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
      else 0

theorem source_original_memory_BIG_density_pair_bilinear434
    (mu : P → ℝ) (V rho : ℝ) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (X Y : BigPhysicalOutput modulus M) :
    sourceOriginalMemoryBigDensityPair434 modulus M B mu V rho shared sigma tau D step X Y =
    sourceOriginalMemoryBigDensityBilinear434 modulus M B mu V rho shared sigma tau D step
      (fun A Z => if A=X ∧ Z=Y then 1 else 0) := by
  classical
  unfold sourceOriginalMemoryBigDensityPair434 sourceOriginalMemoryBigDensityBilinear434
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hp : sourceOriginalMemoryBigProjection434 modulus M B x=X
  <;> by_cases hl : OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c
  <;> by_cases ho : (t,physicalPendingMultiset modulus M B x sigma step c)=Y
  <;> simp only [hp,hl,ho,true_and,false_and,and_true,and_false,ite_true,ite_false,mul_one,mul_zero]

theorem source_original_memory_BIG_density_pair_reverse434
    (mu : P → ℝ) (hmu : ∀ p,0 < mu p) (V rho : ℝ) (hV : 0<V) (hr : 0 ≤ rho)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (X Y : BigPhysicalOutput modulus M) :
    sourceOriginalMemoryBigDensityPair434 modulus M B mu V rho shared sigma tau D step X Y =
    sourceOriginalMemoryBigDensityPair434 modulus M B mu V rho shared tau sigma D (-step) Y X := by
  rw [source_original_memory_BIG_density_pair_bilinear434,
    source_original_memory_BIG_density_pair_bilinear434,
    source_original_memory_BIG_density_bilinear_reverse434 modulus M B mu hmu V rho hV hr]
  congr 1
  funext A Z
  simp only [and_comm]

theorem source_original_memory_BIG_density_pair_shared_support434
    (mu : P → ℝ) (V rho : ℝ) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (X Y : BigPhysicalOutput modulus M)
    (hn : ¬ ∀ i ∈ shared,X.1 (sigma i)=Y.1 (tau i)) :
    sourceOriginalMemoryBigDensityPair434 modulus M B mu V rho shared sigma tau D step X Y=0 := by
  classical
  unfold sourceOriginalMemoryBigDensityPair434
  apply Finset.sum_eq_zero
  intro x hx
  have hi : (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if sourceOriginalMemoryBigProjection434 modulus M B x=X ∧
        OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
        (t,physicalPendingMultiset modulus M B x sigma step c)=Y
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
      else 0)=0 := by
    apply Finset.sum_eq_zero
    intro c hc
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    rintro ⟨hp,hl,ho⟩
    have ha : x.1=X.1 := congrArg Prod.fst hp
    have hb : t=Y.1 := congrArg Prod.fst ho
    apply hn
    intro i h
    simpa only [ha,hb] using hl.shared_copy i h
  rw [hi,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBigFrameDensityColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
variable (M : ℕ) (cap : G → ℕ)

/-- Full BIG column on the original group state and branch carriers.
Its endpoint is a vector of actual active/Fock outputs; no numerical
deduplication of atoms or active labels occurs. -/
def sourceOriginalMemoryBigFrameDensityColumn434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (rho : ℝ)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (y : (g : G) → BigPhysicalOutput (modulus g) M) : ℝ :=
  ∑ x : BigGroupState BP modulus M cap,
    (∏ g : G,sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) (x g)) *
    ∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        (∀ g,( (b g).1,physicalPendingMultiset (modulus g) M (cap g) (x g)
          (sigma g) step (b g).2)=y g)
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0

/-- Exact tensor identity for a fixed output. It follows from the actual
independent harmonic/Fock measures and the literal legal output tests,
and makes no separability assumption about a comparison multiplier. -/
theorem source_original_memory_BIG_FRAME_density_column_product434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (rho : ℝ)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (y : (g : G) → BigPhysicalOutput (modulus g) M) :
    sourceOriginalMemoryBigFrameDensityColumn434 BP modulus M cap mu V rho
      shared sigma tau D step y =
    ∏ g : G,sourceOriginalMemoryBigDensityBilinear434 (modulus g) M (cap g)
      (mu g) (V g) rho (shared g) (sigma g) (tau g) D step
      (fun _ Y => if Y=y g then 1 else 0) := by
  classical
  let w := fun (g : G) (x : BigState (modulus g) M (cap g))
      (z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) x) =>
    if OrientedBigEdgeLegal (modulus g) M (cap g) x z.1 (shared g)
        (sigma g) (tau g) D step z.2 ∧
      (z.1,physicalPendingMultiset (modulus g) M (cap g) x (sigma g) step z.2)=y g
    then ‖orientedBigBranchCoefficient (modulus g) M (cap g) (mu g) (V g) rho
      x z.1 (shared g) (sigma g) (tau g) step z.2‖ else 0
  have hprod (x : BigGroupState BP modulus M cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) :
      (∏ g : G,w g (x g) (b g)) =
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        (∀ g,((b g).1,physicalPendingMultiset (modulus g) M (cap g) (x g)
          (sigma g) step (b g).2)=y g)
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0 := by
    simp only [w,Finset.prod_ite_zero,Finset.mem_univ,forall_const,
      sourceOriginalMemoryBigFrameLegal434,sourceOriginalMemoryBigFrameNorm434,forall_and]
    congr <;> exact Subsingleton.elim _ _
  have hinner (x : BigGroupState BP modulus M cap) :
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
        ∏ g : G,w g (x g) (b g)) =
      ∏ g : G,∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),
        w g (x g) z := by
    convert (Fintype.prod_sum (fun g z => w g (x g) z)).symm using 1 <;>
      congr <;> exact Subsingleton.elim _ _
  unfold sourceOriginalMemoryBigFrameDensityColumn434
  simp_rw [← hprod,hinner,← Finset.prod_mul_distrib]
  have hout :
      (∑ x : BigGroupState BP modulus M cap,
        ∏ g : G,sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) (x g) *
          ∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),
            w g (x g) z) =
      ∏ g : G,∑ x : BigState (modulus g) M (cap g),
        sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) x *
          ∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) x,w g x z := by
    convert (Fintype.prod_sum (fun g (x : BigState (modulus g) M (cap g)) =>
      sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) x *
        ∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) x,w g x z)).symm
      using 1 <;> congr <;> exact Subsingleton.elim _ _
  rw [hout]
  apply Finset.prod_congr rfl
  intro g hg
  unfold sourceOriginalMemoryBigDensityBilinear434
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [w]
  split_ifs <;> simp_all

theorem source_original_memory_BIG_FRAME_density_column434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (V : G → ℝ) (rho R : ℝ) (hV : ∀ g,0<V g) (hr : 0< rho) (hr1 : rho<1)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (d : ℕ)
    (hd : ∀ g,(orientedUnshared M (shared g)).card ≤ d)
    (y : (g : G) → BigPhysicalOutput (modulus g) M) :
    sourceOriginalMemoryBigFrameDensityColumn434 BP modulus M cap mu V rho
      shared sigma tau D step y ≤
    (∏ g : G,(4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d))) *
      ∏ g : G,sourceOriginalMemoryBigDensityOrbitMass434 (modulus g) M (cap g) (mu g) (V g) (y g) := by
  rw [source_original_memory_BIG_FRAME_density_column_product434,← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro g hg
    unfold sourceOriginalMemoryBigDensityBilinear434
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · exact mul_nonneg (bigStateMass_positive (modulus g) M (cap g) (mu g) (hmu g) x).le
        (pow_nonneg (hV g).le _)
    · apply Finset.sum_nonneg
      intro c hc
      apply Finset.sum_nonneg
      intro t ht
      split_ifs <;> positivity
  · intro g hg
    exact source_original_memory_BIG_density_column434 (modulus g) M (cap g) (mu g) (hmu g)
      (V g) rho R (hV g) hr hr1 hR (hMass g) (shared g) (sigma g) (tau g) D step d (hd g) (y g)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBigFrameDensityPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
variable (M : ℕ) (cap : G → ℕ)

/-- Full BIG two-ended kernel on the original group state and branch carriers.
Its endpoint is a vector of actual active/Fock outputs; no numerical
deduplication of atoms or active labels occurs. -/
def sourceOriginalMemoryBigFrameDensityPair434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (rho : ℝ)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (X Y : (g : G) → BigPhysicalOutput (modulus g) M) : ℝ :=
  ∑ x : BigGroupState BP modulus M cap,
    (∏ g : G,sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) (x g)) *
    ∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
      if (∀ g,sourceOriginalMemoryBigProjection434 (modulus g) M (cap g) (x g)=X g) ∧
        sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        (∀ g,( (b g).1,physicalPendingMultiset (modulus g) M (cap g) (x g)
          (sigma g) step (b g).2)=Y g)
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0

/-- Exact tensor identity for a fixed physical endpoint pair. It follows from the actual
independent harmonic/Fock measures and the literal legal output tests,
and makes no separability assumption about a comparison multiplier. -/
theorem source_original_memory_BIG_FRAME_density_pair_product434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (rho : ℝ)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (X Y : (g : G) → BigPhysicalOutput (modulus g) M) :
    sourceOriginalMemoryBigFrameDensityPair434 BP modulus M cap mu V rho
      shared sigma tau D step X Y =
    ∏ g : G,sourceOriginalMemoryBigDensityPair434 (modulus g) M (cap g)
      (mu g) (V g) rho (shared g) (sigma g) (tau g) D step (X g) (Y g) := by
  classical
  let w := fun (g : G) (x : BigState (modulus g) M (cap g))
      (z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) x) =>
    if sourceOriginalMemoryBigProjection434 (modulus g) M (cap g) x=X g ∧
      OrientedBigEdgeLegal (modulus g) M (cap g) x z.1 (shared g)
        (sigma g) (tau g) D step z.2 ∧
      (z.1,physicalPendingMultiset (modulus g) M (cap g) x (sigma g) step z.2)=Y g
    then ‖orientedBigBranchCoefficient (modulus g) M (cap g) (mu g) (V g) rho
      x z.1 (shared g) (sigma g) (tau g) step z.2‖ else 0
  have hprod (x : BigGroupState BP modulus M cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) :
      (∏ g : G,w g (x g) (b g)) =
      if (∀ g,sourceOriginalMemoryBigProjection434 (modulus g) M (cap g) (x g)=X g) ∧
        sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        (∀ g,((b g).1,physicalPendingMultiset (modulus g) M (cap g) (x g)
          (sigma g) step (b g).2)=Y g)
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0 := by
    simp only [w,Finset.prod_ite_zero,Finset.mem_univ,forall_const,
      sourceOriginalMemoryBigFrameLegal434,sourceOriginalMemoryBigFrameNorm434,forall_and]
    congr <;> exact Subsingleton.elim _ _
  have hinner (x : BigGroupState BP modulus M cap) :
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
        ∏ g : G,w g (x g) (b g)) =
      ∏ g : G,∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),
        w g (x g) z := by
    convert (Fintype.prod_sum (fun g z => w g (x g) z)).symm using 1 <;>
      congr <;> exact Subsingleton.elim _ _
  unfold sourceOriginalMemoryBigFrameDensityPair434
  simp_rw [← hprod,hinner,← Finset.prod_mul_distrib]
  have hout :
      (∑ x : BigGroupState BP modulus M cap,
        ∏ g : G,sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) (x g) *
          ∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),
            w g (x g) z) =
      ∏ g : G,∑ x : BigState (modulus g) M (cap g),
        sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) x *
          ∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) x,w g x z := by
    convert (Fintype.prod_sum (fun g (x : BigState (modulus g) M (cap g)) =>
      sourceOriginalMemoryBigDensityMass434 (modulus g) M (cap g) (mu g) (V g) x *
        ∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) x,w g x z)).symm
      using 1 <;> congr <;> exact Subsingleton.elim _ _
  rw [hout]
  apply Finset.prod_congr rfl
  intro g hg
  unfold sourceOriginalMemoryBigDensityPair434
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  rw [Fintype.sum_prod_type,Finset.sum_comm]

/-- Complete multigroup physical orbit-pair reversal. The fixed endpoint
pair is an exact disintegration device, not a factorization of joint K. -/
theorem source_original_memory_BIG_FRAME_density_pair_reverse434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (V : G → ℝ) (rho : ℝ) (hV : ∀ g,0<V g) (hr : 0 ≤ rho)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (X Y : (g : G) → BigPhysicalOutput (modulus g) M) :
    sourceOriginalMemoryBigFrameDensityPair434 BP modulus M cap mu V rho shared sigma tau D step X Y =
    sourceOriginalMemoryBigFrameDensityPair434 BP modulus M cap mu V rho shared tau sigma D (-step) Y X := by
  rw [source_original_memory_BIG_FRAME_density_pair_product434,
    source_original_memory_BIG_FRAME_density_pair_product434]
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_memory_BIG_density_pair_reverse434 (modulus g) M (cap g)
    (mu g) (hmu g) (V g) rho (hV g) hr (shared g) (sigma g) (tau g) D step (X g) (Y g)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryRawComparisonBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Exactly one RAW term and the original two-block nonempty probe pairs. -/
abbrev SourceOriginalMemoryRawComparisonIndex434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G) (m : ℕ) :=
  Option ↥(sourceOriginalTwoBlockProbePatterns434 blockA blockB m)

def sourceOriginalMemoryRawComparisonPattern434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G)
    (J m : ℕ) (hmJ : m ≤ J) :
    SourceOriginalMemoryRawComparisonIndex434 blockA blockB m → SourcePattern G J m
  | none => ⟨fun _ => ∅,by intro g; simp⟩
  | some nu => sourceOriginalProbeMemoryPattern434 J m hmJ nu.val

def sourceOriginalMemoryRawComparisonK434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ) :
    SourcePatternK (fun g => {p : ℕ // p ∈ P g}) J ell m
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) :=
  fun nu => match nu with
  | none => fun _ _ _ => 1
  | some nu => fun aux s t =>
    sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu.val Q
      (hA nu.val) (hB nu.val) xi aux s t

def sourceOriginalMemoryRawComparisonCap434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G)
    (m Q : ℕ) (xi : ℝ) :
    SourceOriginalMemoryRawComparisonIndex434 blockA blockB m → ℝ
  | none => 1
  | some _ => (Q:ℝ)^4*(xi⁻¹)^2

theorem source_original_memory_RAW_COMPARISON_cap_nonneg434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G)
    (m Q : ℕ) (xi : ℝ) (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m) :
    0 ≤ sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu := by
  cases nu <;> dsimp [sourceOriginalMemoryRawComparisonCap434] <;> positivity

/-- The cap is proved for the literal RAW and canonical signed Knu.
No analytic kernel-smallness premise occurs. -/
theorem source_original_memory_RAW_COMPARISON_K_cap434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
    (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
    (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
    (hxi : 0<xi)
    (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ nu))
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    ‖sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
      nu aux s t‖ ≤ sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu := by
  cases nu with
  | none => simp [sourceOriginalMemoryRawComparisonK434,sourceOriginalMemoryRawComparisonCap434]
  | some nu =>
    exact source_original_memory_CANONICAL_K_norm434 P V J ell m hmJ nu.val Q
      (hA nu.val) (hB nu.val) xi (hhA nu.val nu.property) (hhB nu.val nu.property)
      hxi aux s t

/-- RAW plus all original comparisons, paid before J. The count is the
true two-block family count, independent of auxiliary and shared slots. -/
theorem source_original_memory_RAW_COMPARISON_cap_budget434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (L C0 xi : ℝ) (Cq Cxi : ℕ)
    (hL : 2 ≤ L) (hC0 : 0 ≤ C0) (hxi : 0<xi)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ C0*Real.log L)
    (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi) :
    (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
      sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) ≤
      L^((m:ℝ)*C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1) := by
  classical
  have hcap : 0 ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by positivity
  have hc :
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        (Q:ℝ)^4*(xi⁻¹)^2) ≤
      (2^(m*(blockA.card+blockB.card)):ℝ)*((Q:ℝ)^4*(xi⁻¹)^2) := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hcap
    exact_mod_cast source_original_two_block_probe_pattern_card434 blockA blockB m
  have hh := source_original_probe_raw_plus_cost_fixed_power434 blockA blockB m Q
    L C0 xi Cq Cxi hL hC0 hxi hGroups hQ hXi
    (fun _ => (Q:ℝ)^4*(xi⁻¹)^2) hc
  simpa [SourceOriginalMemoryRawComparisonIndex434,
    sourceOriginalMemoryRawComparisonCap434,Fintype.sum_option,
    Finset.sum_coe_sort,add_comm] using hh

/-- The actual SMALL absolute row uses sqrt(q), so its fixed exponent
is explicitly different from the squared-energy exponent. -/
theorem source_original_memory_SMALL_absolute_row_polynomial434
    {SG : Type} [Fintype SG] (ell : ℕ)
    (q vmin C0 L : ℝ) (hq : 0<q) (hq1 : q<1)
    (hv : 0<vmin) (hC0 : 0 ≤ C0) (hL : 1 ≤ L)
    (Vs : SG → ℝ) (hVs : ∀ g,vmin ≤ Vs g)
    (hGroups : (Fintype.card SG:ℝ) ≤ C0*Real.log L) :
    (∏ g : SG,memorySmallRowConstant q (Vs g) ell) ≤
      L^(sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) vmin C0) := by
  have hsq1 : Real.sqrt q < 1 := by
    nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
  have hh := source_original_B26_small_conditioning_polynomial434 ell
    (Real.sqrt q) vmin C0 L (Real.sqrt_pos.mpr hq) hsq1 hv hC0 hL Vs hVs hGroups
  convert hh using 1
  unfold memorySmallGroupConditioningConstant
  apply Finset.prod_congr rfl
  intro g hg
  unfold memorySmallRowConstant
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalOriginalERow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

def sourceOriginalMemoryERowLoss434
    (cfg : SourceComparisonFixed434) (ell Cq Cxi : ℕ) (q : ℝ) : ℝ :=
  sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) cfg.vmin cfg.C0 +
  ((cfg.tmax:ℝ)*cfg.C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1)

/-- Applicable logarithmic saving for the COMPLETE literal original
E absolute row with at least one OLD promotion. RAW, the exact two-block
signed canonical Knu family, every auxiliary draw, both BIG and SMALL
permutation pairs, all target states and ordered OLD injections are
assembled. Fixed conductor/retention losses are paid BEFORE the explicit
J; the eventual threshold precedes all moving physical data. -/
theorem source_original_memory_PHYSICAL_ORIGINAL_E_promotion_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let A := B+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K A
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (st : FullPhysicalState
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (hOldTotal : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalMemoryOriginalEPromotionRow434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho data.Vsmall data.Vbig mu
      (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q hA hB xi) zeta theta o k st ≤ L^(-B) := by
  dsimp only
  let Cs := sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) cfg.vmin cfg.C0
  let C1 : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let A := B+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K A
  have hBig := source_original_memory_PHYSICAL_BIG_rare_promotion_log_saving434
    cfg ell (max Jmin cfg.tmax) hell Ck q rho c0 A hq.le hq1.le hr hr1 hc0
  refine ⟨hBig.1,?_⟩
  filter_upwards [hBig.2,eventually_ge_atTop (2:ℝ)] with L hRare hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap st hSmallUpper hBigLower hHarmonic hSmallGroupsLower hOldTotal
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk
  let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
    (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hLp : 0<L := zero_lt_one.trans_le hL1
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hc : blockA.card+blockB.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hBlocks]
    exact Finset.card_le_univ _
  have hBlocksCap : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    calc
      _ ≤ (Fintype.card G:ℝ) := by exact_mod_cast hc
      _ ≤ _ := data.hBigGroups
  have hKsum0 :
      0 ≤ ∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
        sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu :=
    Finset.sum_nonneg (fun nu _ =>
      source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu)
  have hKsum :
      (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
        sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) ≤ L^C1 := by
    apply (source_original_memory_RAW_COMPARISON_cap_budget434 blockA blockB m Q
      L cfg.C0 xi Cq Cxi hL cfg.hC0 hxi hBlocksCap hQ hXi).trans
    apply Real.rpow_le_rpow_of_exponent_le hL1
    dsimp only [C1]
    have hmR : (m:ℝ) ≤ cfg.tmax := by exact_mod_cast hm
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmR cfg.hC0) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    linarith only [hh]
  have hSmall :
      (∏ g : ι,memorySmallRowConstant q (data.Vsmall g) ell) ≤ L^Cs :=
    source_original_memory_SMALL_absolute_row_polynomial434 ell q cfg.vmin cfg.C0 L
      hq hq1 cfg.hv cfg.hC0 hL1 data.Vsmall data.hVsmall data.hSmallGroups
  have hOuter := source_original_memory_ORIGINAL_E_promotion_outer_bound434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
    J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho data.Vsmall data.Vbig hq hq1 hVs hVb hHarmonic mu
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta o k ho st
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
    (source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi hhA hhB hxi)
    (L^(-A))
    (fun nu aux bs bt => hRare x Y Hprime data sep m hm cap st
      hSmallUpper hBigLower hHarmonic hSmallGroupsLower hOldTotal
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ nu)
      aux bs bt o k ho hk0 hk)
  apply hOuter.trans
  calc
    _ ≤ (L^C1*L^Cs)*L^(-A) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLp.le _)
      exact mul_le_mul hKsum hSmall
        (by
          apply Finset.prod_nonneg
          intro g hg
          have hv := hVs g
          have hs : 0<1-Real.sqrt q := by
            nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
          dsimp only [memorySmallRowConstant]
          positivity)
        (Real.rpow_nonneg hLp.le _)
    _ = L^(-B) := by
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      dsimp only [A,sourceOriginalMemoryERowLoss434,Cs,C1]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalESplit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The disjoint remaining DIRTY component: a store and no promotion. -/
def sourceOriginalMemoryOriginalEStoreOnly434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m cap patterns st o k,
    if (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
      (∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty) then
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
    else 0

/-- The literal no-store/no-promotion part of the full oriented E. -/
def sourceOriginalMemoryOriginalEClean434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m cap patterns st o k,
    if (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) ∧
      (¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty) then
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
    else 0

/-- Exact signed decomposition on the original branch carrier.
Promotion+store branches are counted once, in the promotion component.
This identity does not assert smallness of the store-only component. -/
theorem source_original_memory_ORIGINAL_E_CLEAN_DIRTY_split434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st F =
    sourceOriginalMemoryOriginalEClean434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st F +
    sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st F +
    sourceOriginalMemoryOriginalEStoreOnly434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st F := by
  classical
  unfold fullSourceOrientedPhysicalE sourceOriginalMemoryOriginalEClean434
    sourceOriginalMemoryOriginalEPromotion434 sourceOriginalMemoryOriginalEStoreOnly434
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hp : ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty
  · simp only [hp,not_true_eq_false,false_and,ite_false,ite_true,zero_add,add_zero]
  · by_cases hs : ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty
    · simp only [hp,hs,not_false_eq_true,not_true_eq_false,and_self,true_and,
        ite_true,ite_false,zero_add,add_zero]
    · simp only [hp,hs,not_false_eq_true,and_self,true_and,
        ite_true,ite_false,zero_add,add_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalTransposePromotionRow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Applicable logarithmic saving for the literal original
E absolute row with the transposed joint RAW+comparison K with at least one OLD promotion. RAW, the exact two-block
signed canonical Knu family, every auxiliary draw, both BIG and SMALL
permutation pairs, all target states and ordered OLD injections are
assembled. Fixed conductor/retention losses are paid BEFORE the explicit
J; the eventual threshold precedes all moving physical data. -/
theorem source_original_memory_PHYSICAL_TRANSPOSE_E_promotion_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let A := B+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K A
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (st : FullPhysicalState
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (hOldTotal : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalMemoryOriginalEPromotionRow434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho data.Vsmall data.Vbig mu
      (fun nu aux s t => sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q hA hB xi nu aux t s) zeta theta o k st ≤ L^(-B) := by
  dsimp only
  let Cs := sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) cfg.vmin cfg.C0
  let C1 : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let A := B+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K A
  have hBig := source_original_memory_PHYSICAL_BIG_rare_promotion_log_saving434
    cfg ell (max Jmin cfg.tmax) hell Ck q rho c0 A hq.le hq1.le hr hr1 hc0
  refine ⟨hBig.1,?_⟩
  filter_upwards [hBig.2,eventually_ge_atTop (2:ℝ)] with L hRare hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap st hSmallUpper hBigLower hHarmonic hSmallGroupsLower hOldTotal
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk
  let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
    (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hLp : 0<L := zero_lt_one.trans_le hL1
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hc : blockA.card+blockB.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hBlocks]
    exact Finset.card_le_univ _
  have hBlocksCap : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    calc
      _ ≤ (Fintype.card G:ℝ) := by exact_mod_cast hc
      _ ≤ _ := data.hBigGroups
  have hKsum0 :
      0 ≤ ∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
        sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu :=
    Finset.sum_nonneg (fun nu _ =>
      source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu)
  have hKsum :
      (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
        sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) ≤ L^C1 := by
    apply (source_original_memory_RAW_COMPARISON_cap_budget434 blockA blockB m Q
      L cfg.C0 xi Cq Cxi hL cfg.hC0 hxi hBlocksCap hQ hXi).trans
    apply Real.rpow_le_rpow_of_exponent_le hL1
    dsimp only [C1]
    have hmR : (m:ℝ) ≤ cfg.tmax := by exact_mod_cast hm
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmR cfg.hC0) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    linarith only [hh]
  have hSmall :
      (∏ g : ι,memorySmallRowConstant q (data.Vsmall g) ell) ≤ L^Cs :=
    source_original_memory_SMALL_absolute_row_polynomial434 ell q cfg.vmin cfg.C0 L
      hq hq1 cfg.hv cfg.hC0 hL1 data.Vsmall data.hVsmall data.hSmallGroups
  have hOuter := source_original_memory_ORIGINAL_E_promotion_outer_bound434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
    J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho data.Vsmall data.Vbig hq hq1 hVs hVb hHarmonic mu
    (fun nu aux s t => sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi nu aux t s) zeta theta o k ho st
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
    (fun nu aux s t => source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi hhA hhB hxi nu aux t s)
    (L^(-A))
    (fun nu aux bs bt => hRare x Y Hprime data sep m hm cap st
      hSmallUpper hBigLower hHarmonic hSmallGroupsLower hOldTotal
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ nu)
      aux bs bt o k ho hk0 hk)
  apply hOuter.trans
  calc
    _ ≤ (L^C1*L^Cs)*L^(-A) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLp.le _)
      exact mul_le_mul hKsum hSmall
        (by
          apply Finset.prod_nonneg
          intro g hg
          have hv := hVs g
          have hs : 0<1-Real.sqrt q := by
            nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
          dsimp only [memorySmallRowConstant]
          positivity)
        (Real.rpow_nonneg hLp.le _)
    _ = L^(-B) := by
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      dsimp only [A,sourceOriginalMemoryERowLoss434,Cs,C1]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemorySectorDensityVacuum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Auxiliary OLD-sector density on the genuine symmetric output. -/
def sourceOriginalMemorySectorDensity434 (Vb : BG → ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∏ g : BG,(Vb g)^((y.2 g).2.card)

theorem source_original_memory_sector_density_pos434
    (Vb : BG → ℝ) (hV : ∀ g,0<Vb g)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    0<sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y := by
  apply Finset.prod_pos
  intro g hg
  exact pow_pos (hV g) _

/-- The auxiliary density is one on the actual vacuum support. -/
theorem source_original_memory_sector_density_vacuum434
    (Vb : BG → ℝ) (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y : ℂ) *
      star (physicalVacuum SP smallMod BP bigMod J ell y) =
    star (physicalVacuum SP smallMod BP bigMod J ell y) := by
  by_cases h : ∀ g : BG,(y.2 g).2=0
  · simp [physicalVacuum,h,sourceOriginalMemorySectorDensity434]
  · simp [physicalVacuum,h]

/-- Any actual vacuum pairing, with an arbitrary joint output test,
is unchanged by this auxiliary Hilbert density. -/
theorem source_original_memory_sector_density_vacuum_pairing434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (H : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    (∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      ((physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y : ℝ) : ℂ) *
      star (physicalVacuum SP smallMod BP bigMod J ell y) * H y) =
    physicalSymmetricInner SP smallMod BP bigMod (J+ell) cap Vs mu
      (physicalVacuum SP smallMod BP bigMod J ell) H := by
  unfold physicalSymmetricInner
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Complex.ofReal_mul,mul_assoc,
    source_original_memory_sector_density_vacuum434]

variable (m : ℕ) {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Same original marked chain, source-faithful phases, birth filter,
baseline and vacuum observables; only the displayed boundary Hilbert
measure carries the auxiliary sector density. -/
def sourceOriginalMemorySectorWeightedRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bigMod q N Vb
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      ((physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y : ℝ) : ℂ) *
      star (physicalVacuum SP smallMod BP bigMod J ell y) *
      (if (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup then
        memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
          q rho Vs Vb mu K zeta theta k N N 0
          (fun out _ => physicalVacuum SP smallMod BP bigMod J ell out)
          y (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset
      else 0)

/-- Literal equality with the original full memorySourceRoot. This
justifies the auxiliary measure at vacuum endpoints but proves no
small operator norm, G/birth estimate or arithmetic transference. -/
theorem source_original_memory_SOURCE_ROOT_sector_density434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    sourceOriginalMemorySectorWeightedRoot434 SP smallMod BP bigMod J ell cap m patterns
      q rho Vs Vb K zeta theta k R =
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q rho Vs Vb K zeta theta k R := by
  dsimp only [sourceOriginalMemorySectorWeightedRoot434,memorySourceRoot]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Complex.ofReal_mul,mul_assoc,
    source_original_memory_sector_density_vacuum434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemorySectorDensityOrbit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The auxiliary density on an ordered source is exactly the product
of V_g^j_g for the actual OLD sector sizes. -/
theorem source_original_memory_sector_density_projection434
    (Vb : BG → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) =
    ∏ g : BG,(Vb g)^((x.2 g).2.1.val) := by
  simp [sourceOriginalMemorySectorDensity434,physicalFockProjection,
    Green64Fock.fockMultiset]

/-- Exact descent of the reweighted ordered mass to the genuine Fock
orbit, retaining all original atom multiplicities. -/
theorem source_original_memory_sector_density_orbit_mass434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    (∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J+ell) cap))
        with physicalFockProjection SP smallMod BP bigMod (J+ell) cap x=y,
      fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)) =
    physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y := by
  unfold physicalOrbitMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- The true weighted conditional expectation formed from the auxiliary
ordered and orbit measures. It is not a counting average. -/
def sourceOriginalMemoryDensityOrbitAverage434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℂ :=
  (∑ x ∈ (Finset.univ : Finset
    (FullPhysicalState SP smallMod BP bigMod (J+ell) cap))
      with physicalFockProjection SP smallMod BP bigMod (J+ell) cap x=y,
    ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) : ℝ) : ℂ) * F x) /
  ((physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y : ℝ) : ℂ)

/-- Reweighting by V_g^j_g leaves every actual Fock orbit compression
unchanged. Since F is arbitrary, this applies to the literal marked G
and E rows, without modifying their original harmonic coefficients,
phase/legality data or seen-history filters. It provides no norm bound. -/
theorem source_original_memory_sector_density_orbit_average434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (hV : ∀ g,0<Vb g)
    (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryDensityOrbitAverage434 SP smallMod BP bigMod J ell cap
      Vs Vb mu F y =
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu F y := by
  classical
  have hd : (sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (source_original_memory_sector_density_pos434
      SP smallMod BP bigMod J ell Vb hV y))
  unfold sourceOriginalMemoryDensityOrbitAverage434 fullPhysicalOrbitAverage
  have hs :
      (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J+ell) cap))
          with physicalFockProjection SP smallMod BP bigMod (J+ell) cap x=y,
        ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x *
          sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb
            (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) : ℝ) : ℂ) * F x) =
      (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J+ell) cap))
          with physicalFockProjection SP smallMod BP bigMod (J+ell) cap x=y,
        (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x : ℂ) * F x) *
      (sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y : ℂ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2,Complex.ofReal_mul]
    ring
  rw [hs,Complex.ofReal_mul,mul_div_mul_right _ _ hd]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemorySmallColumnDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]

/-- Column of the actual permuted SMALL Haar kernel. Its scalar is
one; a global joint multiplier must be bounded separately exactly once. -/
theorem source_original_memory_SOURCE_SMALL_group_kernel_column434
    (J ell : ℕ) (q : ℝ) (Vs : SG → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g) (step : ℤ)
    (ss tt : GroupPermFamily (G:=SG) (J+ell)) (y : GroupState SP smallMod (J+ell)) :
    (∑ x : GroupState SP smallMod (J+ell),
      ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt x y‖) ≤
    ∏ g : SG,memorySmallRowConstant q (Vs g) ell := by
  have he (x : GroupState SP smallMod (J+ell)) :
      ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt x y‖ =
      ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
        (-step) (fun _ _ => 1) tt ss y x‖ := by
    rw [groupPermutedKernel_reverse]
    have hh : reverseGroupPermutationKernel (G:=SG) (J+ell) (fun _ _ => (1:ℂ)) =
        (fun _ _ => (1:ℂ)) := by
      funext a b
      simp only [reverseGroupPermutationKernel,star_one]
    rw [norm_star,hh]
  simp_rw [he]
  simpa only [norm_one,one_mul] using
    source_original_memory_SOURCE_SMALL_group_kernel_row434 SP smallMod J ell q Vs
      hq hq1 hVs (-step) (fun _ _ => 1) tt ss y

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

def sourceOriginalMemoryFullDensityMass434 (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) : ℝ :=
  fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vs mu x *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)

theorem source_original_memory_FULL_density_mass_product434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu x =
    groupStateMass SP smallMod (J+ell) Vs *
      ∏ g : BG,sourceOriginalMemoryBigDensityMass434 (bigMod g) (J+ell) (cap g)
        (mu g) (Vb g) (x.2 g) := by
  rw [sourceOriginalMemoryFullDensityMass434,source_original_memory_sector_density_projection434]
  simp only [fullPhysicalMass,bigGroupStateMass,sourceOriginalMemoryBigDensityMass434,
    Finset.prod_mul_distrib,mul_assoc]

theorem source_original_memory_FULL_density_mass_nonneg434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    0 ≤ sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu x := by
  rw [source_original_memory_FULL_density_mass_product434]
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun g _ => (stateMass_positive (smallMod g) (J+ell) (Vs g) (hVs g)).le)
  · apply Finset.prod_nonneg
    intro g hg
    exact mul_nonneg (bigStateMass_positive (bigMod g) (J+ell) (cap g) (mu g) (hmu g) _).le
      (pow_nonneg (hVb g).le _)

/-- Exact product formula for the actual reweighted orbit measure.
There is one genuine SMALL Haar atom and the full BIG ordered-fibre
mass in each group. This is not a comparison with max/min density. -/
theorem source_original_memory_FULL_density_orbit_product434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y =
    groupStateMass SP smallMod (J+ell) Vs *
      ∏ g : BG,sourceOriginalMemoryBigDensityOrbitMass434 (bigMod g) (J+ell) (cap g)
        (mu g) (Vb g) (y.2 g) := by
  classical
  rw [← source_original_memory_sector_density_orbit_mass434]
  change (∑ x ∈ (Finset.univ : Finset
    (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)) with
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap x=y,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu x) = _
  simp_rw [Finset.sum_filter,source_original_memory_FULL_density_mass_product434]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have he (xb : BigGroupState BP bigMod (J+ell) cap) :
      (∑ xs : GroupState SP smallMod (J+ell),
        if physicalFockProjection SP smallMod BP bigMod (J+ell) cap (xs,xb)=y then
          groupStateMass SP smallMod (J+ell) Vs *
            ∏ g : BG,sourceOriginalMemoryBigDensityMass434 (bigMod g) (J+ell) (cap g)
              (mu g) (Vb g) (xb g) else 0) =
      groupStateMass SP smallMod (J+ell) Vs *
        ∏ g : BG,if sourceOriginalMemoryBigProjection434 (bigMod g) (J+ell) (cap g) (xb g)=y.2 g
          then sourceOriginalMemoryBigDensityMass434 (bigMod g) (J+ell) (cap g)
            (mu g) (Vb g) (xb g) else 0 := by
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ,forall_const]
    by_cases hb : ∀ g,sourceOriginalMemoryBigProjection434 (bigMod g) (J+ell) (cap g) (xb g)=y.2 g
    · rw [if_pos hb]
      have hb' : (fun g => ((xb g).1,Green64Fock.fockMultiset (xb g).2))=y.2 := funext hb
      have hpair (xs : GroupState SP smallMod (J+ell)) :
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap (xs,xb)=y ↔ xs=y.1 := by
        change (xs,fun g => ((xb g).1,Green64Fock.fockMultiset (xb g).2))=y ↔ xs=y.1
        rw [Prod.ext_iff]
        simp only [hb',and_true]
      simp_rw [hpair]
      simp
    · rw [if_neg hb,mul_zero]
      have hb' : (fun g => ((xb g).1,Green64Fock.fockMultiset (xb g).2)) ≠ y.2 :=
        fun h => hb (fun g => congrFun h g)
      apply Finset.sum_eq_zero
      intro xs hxs
      apply if_neg
      intro h
      exact hb' (congrArg Prod.snd h)
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  unfold sourceOriginalMemoryBigDensityOrbitMass434
  convert (Fintype.prod_sum (fun g (x : BigState (bigMod g) (J+ell) (cap g)) =>
    if sourceOriginalMemoryBigProjection434 (bigMod g) (J+ell) (cap g) x=y.2 g then
      sourceOriginalMemoryBigDensityMass434 (bigMod g) (J+ell) (cap g) (mu g) (Vb g) x else 0)).symm
    using 1 <;> congr <;> exact Subsingleton.elim _ _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalColumnTerm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The literal source divisor evaluated on the actual output active
marks. OLD representatives and cutoff choices do not enter it. -/
def sourceOriginalMemoryOutputD434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (bt : BigGroupPerm (BG:=BG) (J+ell)) (tt : GroupPermFamily (G:=SG) (J+ell)) : ℕ :=
  (∏ g : SG,∏ i ∈ sourceSmallShared J ell g,
    smallMod g (marks (smallMod g) (J+ell) (y.1 g) (tt g i))) *
  (∏ g : BG,
    (∏ i ∈ sourceBigShared J ell m pat g,bigMod g ((y.2 g).1 (bt g i))) *
    (∏ j : ↥(pat.free g),bigMod g (aux g j)))

/-- On every original legal branch the moving source D equals the
literal output D. This invokes the already checked actual reversal;
no independent D is substituted into the C6/source phase. -/
theorem source_original_memory_ORIGINAL_output_D434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z) :
    sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns z.1) z.2.1
      (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
      z.2.2.1.tauBig z.2.2.2.2 =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap (patterns z.1) z.2.1
      st z.2.2.1.sigmaBig z.2.2.2.1 := by
  have hh := source_original_memory_actual_divisor_reverse434 SP smallMod BP bigMod
    J ell m cap patterns st o k z hz
  simpa only [sourceOriginalMemoryOutputD434,sourceOrientedPhysicalD,
    sourceOriginalMemoryActualOrderedOutput434,sourceOrientedPhysicalOutput,
    fullPhysicalBranchOutput,bigGroupBranchOutput,physicalBranchOutput] using hh

/-- Pointwise column domination for the LITERAL original coefficient.
All Fourier/Mellin factors and the arbitrary joint K are retained on
the left. Its proved joint cap is charged once; shared legality freezes
the common D and signed o*k*D at the actual output on the right. -/
theorem source_original_memory_ORIGINAL_column_coefficient434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2)
    (zs : GroupState SP smallMod (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : ℝ)
    (hK : ∀ s t,‖Knu nu aux s t‖ ≤ Kcap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k
      (sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs))
    (hout : sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k
      (sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs)=y) :
    let Dy := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux y bt tt
    let delta := o*k*(Dy:ℤ)
    ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu
      Knu zeta theta o k st (sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs)‖ ≤
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ * Kcap *
    sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
      (sourceBigShared J ell m (patterns nu)) bs bt delta b *
    ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
      delta (fun _ _ => 1) ss tt st.1 y.1‖ := by
  classical
  dsimp only
  let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
    J ell m cap patterns nu aux st bs bt ss tt b zs
  let Dy := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux y bt tt
  let delta := o*k*(Dy:ℤ)
  have hD : sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      (patterns nu) aux st bs ss=Dy := by
    have hh := source_original_memory_ORIGINAL_output_D434 SP smallMod BP bigMod
      J ell m cap patterns st o k z hz
    rw [hout] at hh
    exact hh.symm
  have hstep : sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns nu) aux st bs ss o k=delta := by
    unfold sourceOrientedStep
    rw [hD]
  have hzs : zs=y.1 := congrArg Prod.fst hout
  have hs : groupEdgeAllowedPerm SP smallMod (J+ell) (sourceSmallShared J ell)
      delta ss tt st.1 y.1 := by
    simpa only [z,sourceOriginalMemoryFixedPhysicalChoice434,hstep,hzs] using hz.2.2.2.2
  have hscalar : ‖originalEdgeScalar
      (Knu nu aux (fun g i => (st.2 g).1 (bs g i)) (fun g i => (b g).1 (bt g i)))
      zeta theta Dy o k‖ ≤ Kcap := by
    rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ hz.1]
    exact hK _ _
  have hn :
      ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu
        Knu zeta theta o k st z‖ =
      (‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
        (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
        (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
        sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
          (sourceBigShared J ell m (patterns nu)) bs bt delta b) *
      (‖originalEdgeScalar
        (Knu nu aux (fun g i => (st.2 g).1 (bs g i)) (fun g i => (b g).1 (bt g i)))
        zeta theta Dy o k‖ *
        ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
          delta (fun _ _ => 1) ss tt st.1 y.1‖) := by
    dsimp only [z,sourceOriginalMemoryFixedPhysicalChoice434,sourceOrientedPhysicalCoefficient]
    rw [hD,hstep,hzs]
    simp only [groupPermutedKernel,if_pos hs,one_mul,norm_mul,norm_prod,
      sourceOriginalMemoryBigFrameNorm434]
  rw [hn]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hscalar (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
    _ = _ := by
      dsimp only [sourceOriginalMemoryBigFrameNorm434,delta,Dy]
      ring
end Green64Analytic.CorrelationSquare

end

end

