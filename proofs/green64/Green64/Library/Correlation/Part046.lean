module

public import Green64.Library.Correlation.Part045
public import Green64.Library.Weights.Part015

@[expose] public section

/-!
# Correlation / Part046

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOriginalColumnPacket -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 28000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalMemoryOriginalColumnPacket434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
    ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
    ∑ zs : GroupState SP smallMod (J+ell),
      let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs
      if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

/-- Complete literal SMALL×BIG column for one original sampled outer
frame. The moving D is frozen at its actual output by legality. All
OLD sectors, target states and branch multiplicities are integrated. -/
theorem source_original_memory_ORIGINAL_column_packet434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho R : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0<q) (hq1 : q<1) (hr : 0< rho) (hr1 : rho<1)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : ℝ) (hK0 : 0 ≤ Kcap) (hK : ∀ s t,‖Knu nu aux s t‖ ≤ Kcap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalColumnPacket434 SP smallMod BP bigMod J ell m cap
      patterns nu aux bs bt ss tt q rho Vs Vb mu Knu zeta theta o k y ≤
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ * Kcap *
    (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    (∏ g : BG,(4:ℝ)^(ell+m) * (memoryPromotionDampingConstant rho (ell+m) *
      ((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m)))) *
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y) := by
  classical
  let Dy := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux y bt tt
  let delta := o*k*(Dy:ℤ)
  let W := ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  let sm := fun xs => ‖groupPermutedKernel SP smallMod (J+ell) q Vs
    (sourceSmallShared J ell) delta (fun _ _ => 1) ss tt xs y.1‖
  let good := fun (xb : BigGroupState BP bigMod (J+ell) cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap xb) =>
    sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap xb
      (sourceBigShared J ell m (patterns nu)) bs bt Dy delta b ∧
      (∀ g,((b g).1,physicalPendingMultiset (bigMod g) (J+ell) (cap g) (xb g)
        (bs g) delta (b g).2)=y.2 g)
  let bn := fun (xb : BigGroupState BP bigMod (J+ell) cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap xb) =>
    sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap xb mu Vb rho
      (sourceBigShared J ell m (patterns nu)) bs bt delta b
  let br := fun xb => ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap xb,
    if good xb b then bn xb b else 0
  have hbr0 (xb) : 0 ≤ br xb := Finset.sum_nonneg (fun b _ => by
    split_ifs
    · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    · exact le_rfl)
  have hrow (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
      ∑ zs : GroupState SP smallMod (J+ell),
        let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
          J ell m cap patterns nu aux st bs bt ss tt b zs
        if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
          sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=y
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ else 0) ≤
      (W*Kcap*sm st.1)*br st.2 := by
    rw [show (W*Kcap*sm st.1)*br st.2 =
      ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        (W*Kcap*sm st.1)*(if good st.2 b then bn st.2 b else 0) by
          exact Finset.mul_sum _ _ _]
    apply Finset.sum_le_sum
    intro b hb
    calc
      _ ≤ ∑ zs : GroupState SP smallMod (J+ell),
          if zs=y.1 then (W*Kcap*sm st.1)*(if good st.2 b then bn st.2 b else 0) else 0 := by
        apply Finset.sum_le_sum
        intro zs hzs
        dsimp only
        by_cases hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k
            (sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
              J ell m cap patterns nu aux st bs bt ss tt b zs) ∧
          sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k
            (sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
              J ell m cap patterns nu aux st bs bt ss tt b zs)=y
        · rw [if_pos hz]
          obtain ⟨hl,ho⟩ := hz
          let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
            J ell m cap patterns nu aux st bs bt ss tt b zs
          have hD : sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
              (patterns nu) aux st bs ss=Dy := by
            have hh := source_original_memory_ORIGINAL_output_D434 SP smallMod BP bigMod
              J ell m cap patterns st o k z hl
            rw [ho] at hh
            exact hh.symm
          have hstep : sourceOrientedStep SP smallMod BP bigMod J ell m cap
              (patterns nu) aux st bs ss o k=delta := by
            unfold sourceOrientedStep
            rw [hD]
          have hzs' : zs=y.1 := congrArg Prod.fst ho
          have hg : good st.2 b := by
            constructor
            · simpa only [z,sourceOriginalMemoryFixedPhysicalChoice434,hD,hstep,
                sourceOriginalMemoryBigFrameLegal434] using hl.2.2.2.1
            · intro g
              have hh := congrFun (congrArg Prod.snd ho) g
              simpa only [sourceOrientedPhysicalOutput,sourceOriginalMemoryFixedPhysicalChoice434,
                fullPhysicalBranchOutput,bigGroupBranchOutput,physicalBranchOutput,hstep] using hh
          rw [if_pos hzs',if_pos hg]
          have hh := source_original_memory_ORIGINAL_column_coefficient434 SP smallMod BP bigMod
            J ell m cap patterns nu aux st bs bt ss tt b zs q rho Vs Vb mu Knu zeta theta o k
            Kcap hK y hl ho
          exact hh.trans_eq (by dsimp only [W,sm,bn,Dy,delta];ring)
        · rw [if_neg hz]
          dsimp only [W,sm,bn,sourceOriginalMemoryBigFrameNorm434]
          split_ifs <;> positivity
      _ = _ := by simp
  let ms := groupStateMass SP smallMod (J+ell) Vs
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let Cb := ∏ g : BG,(4:ℝ)^(ell+m) * (memoryPromotionDampingConstant rho (ell+m) *
    ((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m)))
  let mb := ∏ g : BG,sourceOriginalMemoryBigDensityOrbitMass434 (bigMod g) (J+ell) (cap g)
    (mu g) (Vb g) (y.2 g)
  let cb := sourceOriginalMemoryBigFrameDensityColumn434 BP bigMod (J+ell) cap mu Vb rho
    (sourceBigShared J ell m (patterns nu)) bs bt Dy delta y.2
  have hms : 0 ≤ ms := Finset.prod_nonneg
    (fun g _ => (stateMass_positive (smallMod g) (J+ell) (Vs g) (hVs g)).le)
  have hs : (∑ xs,sm xs) ≤ Cs :=
    source_original_memory_SOURCE_SMALL_group_kernel_column434 SP smallMod J ell q Vs hq hq1 hVs
      delta ss tt y.1
  have hCs : 0 ≤ Cs := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hs
  have hcb : cb ≤ Cb*mb := source_original_memory_BIG_FRAME_density_column434 BP bigMod
    (J+ell) cap mu hmu Vb rho R hVb hr hr1 hR hMass
    (sourceBigShared J ell m (patterns nu)) bs bt Dy delta (ell+m)
    (fun g => memory_source_unshared_count J ell m (patterns nu) g) y.2
  have hcb0 : 0 ≤ cb := by
    apply Finset.sum_nonneg
    intro xb hxb
    exact mul_nonneg (Finset.prod_nonneg (fun g _ =>
      mul_nonneg (bigStateMass_positive (bigMod g) (J+ell) (cap g) (mu g) (hmu g) (xb g)).le
        (pow_nonneg (hVb g).le _))) (hbr0 xb)
  unfold sourceOriginalMemoryOriginalColumnPacket434
  calc
    _ ≤ ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
          ((W*Kcap*sm st.1)*br st.2) :=
      Finset.sum_le_sum (fun st _ => mul_le_mul_of_nonneg_left (hrow st)
        (source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod J ell cap
          Vs Vb mu hVs hVb hmu st))
    _ = (W*Kcap*ms)*((∑ xs,sm xs)*cb) := by
      simp_rw [source_original_memory_FULL_density_mass_product434]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs hxs
      dsimp only [cb,sourceOriginalMemoryBigFrameDensityColumn434]
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xb hxb
      dsimp only [ms,br,good,bn]
      ring
    _ ≤ (W*Kcap*ms)*(Cs*(Cb*mb)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hs hcb hcb0 hCs)
        (mul_nonneg (mul_nonneg (norm_nonneg _) hK0) hms)
    _ = _ := by
      rw [source_original_memory_FULL_density_orbit_product434]
      dsimp only [W,ms,Cs,Cb,mb]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 28000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Absolute coefficient column of the complete literal original E
under the auxiliary density. All nu, auxiliary, endpoint permutations,
physical states and legal branch witnesses remain in this finite sum. -/
def sourceOriginalMemoryOriginalDensityColumn434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
    ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

theorem source_original_memory_ORIGINAL_column_packets434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k y =
    ∑ nu : Nu,∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
    ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryOriginalColumnPacket434 SP smallMod BP bigMod J ell m cap
        patterns nu aux bs bt ss tt q rho Vs Vb mu Knu zeta theta o k y := by
  classical
  letI (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
      Fintype (sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) := inferInstance
  letI : Fintype (Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 ×
        GroupState SP smallMod (J+ell)) := inferInstance
  letI (nu : Nu) : Fintype (SourceBigAux BP J m (patterns nu)) := inferInstance
  let e :
      (Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) ≃
      (Σ nu : Nu,SourceBigAux BP J m (patterns nu) ×
        BigGroupPerm (BG:=BG) (J+ell) × BigGroupPerm (BG:=BG) (J+ell) ×
        GroupPermFamily (G:=SG) (J+ell) × GroupPermFamily (G:=SG) (J+ell) ×
        (Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
          sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 ×
            GroupState SP smallMod (J+ell))) :=
    { toFun := fun ⟨st,nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩ => ⟨nu,aux,bs,bt,ss,tt,st,b,zs⟩
      invFun := fun ⟨nu,aux,bs,bt,ss,tt,st,b,zs⟩ => ⟨st,nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩
      left_inv := by rintro ⟨st,nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩;rfl
      right_inv := by rintro ⟨nu,aux,bs,bt,ss,tt,st,b,zs⟩;rfl }
  let w := fun (z : Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) =>
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu z.1 *
      (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns z.1 o k z.2 ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns z.1 o k z.2=y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k z.1 z.2‖ else 0)
  have he := Fintype.sum_equiv e w (fun z => w (e.symm z))
    (by intro z;rw [e.symm_apply_apply])
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,
    sourceOriginalMemoryOriginalDensityColumn434,sourceOriginalMemoryOriginalColumnPacket434,
    sourceOriginalMemoryFixedPhysicalChoice434,Finset.mul_sum,w,e,Equiv.coe_fn_symm_mk] at he ⊢
  convert he using 1 <;> congr <;> exact Subsingleton.elim _ _

/-- Both actual endpoint averages, and the original harmonic auxiliary
law, integrate to one. No slot count, label count or cell count is paid. -/
theorem source_original_memory_ALL_OUTER_total_mass434
    (Vb : BG → ℝ) (hVb : ∀ g,0<Vb g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bigMod g p:ℝ)=Vb g)
    (pat : SourcePattern BG J m) :
    (∑ aux : SourceBigAux BP J m pat,
    ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
    ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
      ‖(sourceAuxMass BP bigMod J m Vb pat aux:ℂ) *
        (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
        (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖)=1 := by
  classical
  let n : ℝ := Fintype.card (GroupPermFamily (G:=SG) (J+ell))
  let pm := groupPermutationPairMass (G:=SG) (J+ell)
  have hpm : 0 ≤ pm := (groupPermutationPairMass_positive (G:=SG) (J+ell)).le
  have hn : pm*n^2=1 := by
    dsimp only [pm,n]
    exact_mod_cast groupPermutationPairMass_normalized (G:=SG) (J+ell)
  have he (aux : SourceBigAux BP J m pat) :
      (∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
        ‖(sourceAuxMass BP bigMod J m Vb pat aux:ℂ) *
          (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
          (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖) =
      ‖(sourceAuxMass BP bigMod J m Vb pat aux:ℂ) *
        (bigEndpointPairMass (BG:=BG) (J+ell):ℂ)‖ := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg hpm]
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    change n*(n*(_*pm))=_
    calc
      _ = (|sourceAuxMass BP bigMod J m Vb pat aux| *
        |bigEndpointPairMass (BG:=BG) (J+ell)|)*(pm*n^2) := by ring
      _ = _ := by rw [hn,mul_one]
  simp_rw [he]
  exact source_original_memory_BIG_AUX_total_mass434 BP bigMod J ell m Vb hVb hHarmonic pat

/-- Complete source E column bound in the auxiliary physical Hilbert
measure. hK is only a pointwise joint cap, discharged for the canonical
RAW+comparison family separately; no column, Gram, or saving premise is
assumed. The statement is uniform in all finite physical carriers. -/
theorem source_original_memory_ORIGINAL_E_density_column434
    (q rho R : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0<q) (hq1 : q<1) (hr : 0< rho) (hr1 : rho<1)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bigMod g p:ℝ)=Vb g)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖Knu nu aux s t‖ ≤ Kcap nu)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k y ≤
    (∑ nu : Nu,Kcap nu) * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    (∏ g : BG,(4:ℝ)^(ell+m) * (memoryPromotionDampingConstant rho (ell+m) *
      ((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m)))) *
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
      sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y) := by
  classical
  rw [source_original_memory_ORIGINAL_column_packets434]
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let Cb := ∏ g : BG,(4:ℝ)^(ell+m) * (memoryPromotionDampingConstant rho (ell+m) *
    ((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m)))
  let my := physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y
  change _ ≤ (∑ nu,Kcap nu)*Cs*Cb*my
  rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro nu hnu
  let W := fun aux : SourceBigAux BP J m (patterns nu) =>
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  calc
    _ ≤ ∑ aux : SourceBigAux BP J m (patterns nu),
        ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
        ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
        W aux*(Kcap nu*Cs*Cb*my) := by
      apply Finset.sum_le_sum
      intro aux haux
      apply Finset.sum_le_sum
      intro bs hbs
      apply Finset.sum_le_sum
      intro bt hbt
      apply Finset.sum_le_sum
      intro ss hss
      apply Finset.sum_le_sum
      intro tt htt
      exact (source_original_memory_ORIGINAL_column_packet434 SP smallMod BP bigMod J ell m cap
        patterns nu aux bs bt ss tt q rho R Vs Vb mu hq hq1 hr hr1 hVs hVb hmu
        hR hMass Knu zeta theta o k (Kcap nu) (hK0 nu) (hK nu aux) y).trans_eq (by
          dsimp only [W,Cs,Cb,my];ring)
    _ = _ := by
      simp_rw [← Finset.sum_mul]
      rw [source_original_memory_ALL_OUTER_total_mass434 (SG:=SG) BP bigMod
        J ell m Vb hVb hHarmonic (patterns nu),one_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPairGeometry -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (pat : SourcePattern BG J m)

def sourceOriginalMemoryPairAuxBan434
    (aux : SourceBigAux BP J m pat)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : Prop :=
  ∀ (g : BG) (j : ↥(pat.free g)) (i : Fin (J+ell)),
    aux g j ≠ (X.2 g).1 i ∧ aux g j ≠ (Y.2 g).1 i

def sourceOriginalMemoryPairShared434
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : Prop :=
  (∀ g : SG,∀ i ∈ sourceSmallShared J ell g,
    marks (smallMod g) (J+ell) (X.1 g) (ss g i)=marks (smallMod g) (J+ell) (Y.1 g) (tt g i)) ∧
  (∀ g : BG,∀ i ∈ sourceBigShared J ell m pat g,
    (X.2 g).1 (bs g i)=(Y.2 g).1 (bt g i))

theorem source_original_memory_PAIR_aux_reverse434
    (aux : SourceBigAux BP J m pat)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryPairAuxBan434 SP smallMod BP bigMod J ell m pat aux X Y ↔
    sourceOriginalMemoryPairAuxBan434 SP smallMod BP bigMod J ell m pat aux Y X := by
  simp only [sourceOriginalMemoryPairAuxBan434,and_comm]

theorem source_original_memory_PAIR_shared_reverse434
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryPairShared434 SP smallMod BP bigMod J ell m pat bs bt ss tt X Y ↔
    sourceOriginalMemoryPairShared434 SP smallMod BP bigMod J ell m pat bt bs tt ss Y X := by
  constructor
  · rintro ⟨hs,hb⟩
    exact ⟨fun g i hi => (hs g i hi).symm,fun g i hi => (hb g i hi).symm⟩
  · rintro ⟨hs,hb⟩
    exact ⟨fun g i hi => (hs g i hi).symm,fun g i hi => (hb g i hi).symm⟩

/-- The ORIGINAL moving divisor agrees at both physical endpoints
under their exact shared-prime tests. No OLD representative is chosen. -/
theorem source_original_memory_PAIR_D_reverse434
    (aux : SourceBigAux BP J m pat)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (hs : sourceOriginalMemoryPairShared434 SP smallMod BP bigMod J ell m pat bs bt ss tt X Y) :
    sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m pat aux X bs ss =
    sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m pat aux Y bt tt := by
  unfold sourceOriginalMemoryOutputD434
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro i hi
    rw [hs.1 g i hi]
  · apply Finset.prod_congr rfl
    intro g hg
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hs.2 g i hi]

theorem source_original_memory_PAIR_small_norm_reverse434
    (q : ℝ) (Vs : SG → ℝ) (step : ℤ)
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (X Y : GroupState SP smallMod (J+ell)) :
    ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
      step (fun _ _ => 1) ss tt X Y‖ =
    ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
      (-step) (fun _ _ => 1) tt ss Y X‖ := by
  rw [groupPermutedKernel_reverse,norm_star]
  have he : reverseGroupPermutationKernel (G:=SG) (J+ell) (fun _ _ => (1:ℂ)) =
      (fun _ _ => (1:ℂ)) := by
    funext a b
    simp only [reverseGroupPermutationKernel,star_one]
  rw [he]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryEnvelopeFramePair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (pat : SourcePattern BG J m)

def sourceOriginalMemoryEnvelopePairGate434
    (aux : SourceBigAux BP J m pat)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell)) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : Prop :=
  (o=1 ∨ o= -1) ∧ k≠0 ∧
  sourceOriginalMemoryPairAuxBan434 SP smallMod BP bigMod J ell m pat aux X Y ∧
  sourceOriginalMemoryPairShared434 SP smallMod BP bigMod J ell m pat bs bt ss tt X Y ∧
  groupEdgeAllowedPerm SP smallMod (J+ell) (sourceSmallShared J ell)
    (o*k*(sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m pat aux X bs ss:ℤ))
    ss tt X.1 Y.1

theorem source_original_memory_ENVELOPE_pair_gate_reverse_forward434
    (aux : SourceBigAux BP J m pat)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell)) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (h : sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m pat
      aux bs bt ss tt o k X Y) :
    sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m pat
      aux bt bs tt ss (-o) k Y X := by
  rcases h with ⟨ho,hk,ha,hs,hm⟩
  have hd := source_original_memory_PAIR_D_reverse434 SP smallMod BP bigMod J ell m pat
    aux bs bt ss tt X Y hs
  refine ⟨by omega,hk,
    (source_original_memory_PAIR_aux_reverse434 SP smallMod BP bigMod J ell m pat aux X Y).mp ha,
    (source_original_memory_PAIR_shared_reverse434 SP smallMod BP bigMod J ell m pat
      bs bt ss tt X Y).mp hs,?_⟩
  have hh := (groupEdgeAllowedPerm_reverse SP smallMod (J+ell) (sourceSmallShared J ell)
    (o*k*(sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m pat aux X bs ss:ℤ))
    ss tt X.1 Y.1).mp hm
  simpa only [hd,neg_mul] using hh

theorem source_original_memory_ENVELOPE_pair_gate_reverse434
    (aux : SourceBigAux BP J m pat)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell)) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m pat
      aux bs bt ss tt o k X Y ↔
    sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m pat
      aux bt bs tt ss (-o) k Y X := by
  constructor
  · exact source_original_memory_ENVELOPE_pair_gate_reverse_forward434 SP smallMod BP bigMod
      J ell m pat aux bs bt ss tt o k X Y
  · intro h
    simpa only [neg_neg] using source_original_memory_ENVELOPE_pair_gate_reverse_forward434
      SP smallMod BP bigMod J ell m pat aux bt bs tt ss (-o) k Y X h

/-- Explicit physical two-endpoint envelope for one original outer
frame. Its literal coefficient disintegration is established separately. -/
def sourceOriginalMemoryEnvelopeFramePair434 (cap : BG → ℕ)
    (aux : SourceBigAux BP J m pat)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Kcap : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  let D := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m pat aux X bs ss
  let step := o*k*(D:ℤ)
  if sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m pat
      aux bs bt ss tt o k X Y then
    ‖(sourceAuxMass BP bigMod J m Vb pat aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ * Kcap *
    groupStateMass SP smallMod (J+ell) Vs *
    ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
      step (fun _ _ => 1) ss tt X.1 Y.1‖ *
    sourceOriginalMemoryBigFrameDensityPair434 BP bigMod (J+ell) cap mu Vb rho
      (sourceBigShared J ell m pat) bs bt D step X.2 Y.2
  else 0

/-- Reversal includes actual D, SMALL translation, auxiliary endpoint
bans, all BIG Fock sectors and the independent endpoint permutations. -/
theorem source_original_memory_ENVELOPE_frame_pair_reverse434
    (cap : BG → ℕ) (aux : SourceBigAux BP J m pat)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hmu : ∀ g p,0 < mu g p) (hVb : ∀ g,0<Vb g) (hr : 0 ≤ rho)
    (Kcap : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryEnvelopeFramePair434 SP smallMod BP bigMod J ell m pat cap
      aux bs bt ss tt q rho Vs Vb mu Kcap o k X Y =
    sourceOriginalMemoryEnvelopeFramePair434 SP smallMod BP bigMod J ell m pat cap
      aux bt bs tt ss q rho Vs Vb mu Kcap (-o) k Y X := by
  classical
  have hg := source_original_memory_ENVELOPE_pair_gate_reverse434 SP smallMod BP bigMod
    J ell m pat aux bs bt ss tt o k X Y
  unfold sourceOriginalMemoryEnvelopeFramePair434
  by_cases h : sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m pat
      aux bs bt ss tt o k X Y
  · rw [if_pos h,if_pos (hg.mp h)]
    have hd := source_original_memory_PAIR_D_reverse434 SP smallMod BP bigMod J ell m pat
      aux bs bt ss tt X Y h.2.2.2.1
    rw [← hd]
    simp only [neg_mul]
    rw [source_original_memory_PAIR_small_norm_reverse434 SP smallMod J ell q Vs
      (o*k*(sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m pat aux X bs ss:ℤ))
      ss tt X.1 Y.1,
      source_original_memory_BIG_FRAME_density_pair_reverse434 BP bigMod (J+ell) cap
        mu hmu Vb rho hVb hr]
  · rw [if_neg h,if_neg (fun h' => h (hg.mpr h'))]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalPairTerm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 28000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact coefficient norm, with the whole original joint K evaluated
at its actual BIG endpoints. No separability or majorant is assumed. -/
theorem source_original_memory_ORIGINAL_coefficient_norm_factor434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2)
    (zs : GroupState SP smallMod (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) :
    let delta := sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns nu) aux st bs ss o k
    ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st
      (sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs)‖ =
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
    ‖Knu nu aux (fun g i => (st.2 g).1 (bs g i)) (fun g i => (b g).1 (bt g i))‖ *
    sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
      (sourceBigShared J ell m (patterns nu)) bs bt delta b *
    ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
      delta (fun _ _ => 1) ss tt st.1 zs‖ := by
  classical
  dsimp only [sourceOriginalMemoryFixedPhysicalChoice434,sourceOrientedPhysicalCoefficient]
  simp only [groupPermutedKernel]
  split_ifs
  · simp only [norm_mul,norm_prod,one_mul,sourceOriginalMemoryBigFrameNorm434,
      source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
    ring
  · simp only [mul_zero,norm_zero]

/-- Source D is literally a function of the physical input orbit. -/
theorem source_original_memory_ORIGINAL_input_D434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bs : BigGroupPerm (BG:=BG) (J+ell)) (ss : GroupPermFamily (G:=SG) (J+ell)) :
    sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap st) bs ss =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap (patterns nu) aux st bs ss := rfl

/-- Exact legality disintegration at two full physical endpoints.
The actual moving divisor, auxiliary bans, SMALL congruences and all
BIG OLD/store/promotion restrictions are retained. -/
theorem source_original_memory_ORIGINAL_pair_legal434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2)
    (zs : GroupState SP smallMod (J+ell)) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    let D := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux X bs ss
    let delta := o*k*(D:ℤ)
    let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bs bt ss tt b zs
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
      sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y) ↔
    (st.1=X.1 ∧ zs=Y.1 ∧
      sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m (patterns nu)
        aux bs bt ss tt o k X Y ∧
      (∀ g,sourceOriginalMemoryBigProjection434 (bigMod g) (J+ell) (cap g) (st.2 g)=X.2 g) ∧
      sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m (patterns nu)) bs bt D delta b ∧
      (∀ g,((b g).1,physicalPendingMultiset (bigMod g) (J+ell) (cap g) (st.2 g)
        (bs g) delta (b g).2)=Y.2 g)) := by
  classical
  dsimp only
  let D := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux X bs ss
  let delta := o*k*(D:ℤ)
  let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
    J ell m cap patterns nu aux st bs bt ss tt b zs
  have hd (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X) :
      sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap (patterns nu) aux st bs ss=D := by
    rw [← source_original_memory_ORIGINAL_input_D434 SP smallMod BP bigMod J ell m cap
      patterns nu aux st bs ss,hx]
  have hdelta (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X) :
      sourceOrientedStep SP smallMod BP bigMod J ell m cap (patterns nu) aux st bs ss o k=delta := by
    unfold sourceOrientedStep
    rw [hd hx]
  constructor
  · rintro ⟨hx,hl,hy⟩
    have hxs : st.1=X.1 := congrArg Prod.fst hx
    have hxb (g) : sourceOriginalMemoryBigProjection434 (bigMod g) (J+ell) (cap g) (st.2 g)=X.2 g :=
      congrFun (congrArg Prod.snd hx) g
    have hzs : zs=Y.1 := congrArg Prod.fst hy
    have hyb (g) : ((b g).1,physicalPendingMultiset (bigMod g) (J+ell) (cap g) (st.2 g)
        (bs g) delta (b g).2)=Y.2 g := by
      simpa only [sourceOrientedPhysicalOutput,sourceOriginalMemoryFixedPhysicalChoice434,
        fullPhysicalBranchOutput,bigGroupBranchOutput,physicalBranchOutput,hdelta hx] using
        congrFun (congrArg Prod.snd hy) g
    have hg : sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m (patterns nu)) bs bt D delta b := by
      simpa only [sourceOriginalMemoryFixedPhysicalChoice434,hd hx,hdelta hx,
        sourceOriginalMemoryBigFrameLegal434] using hl.2.2.2.1
    have hm : groupEdgeAllowedPerm SP smallMod (J+ell) (sourceSmallShared J ell)
        delta ss tt X.1 Y.1 := by
      simpa only [sourceOriginalMemoryFixedPhysicalChoice434,hdelta hx,hxs,hzs] using hl.2.2.2.2
    refine ⟨hxs,hzs,⟨hl.1,hl.2.1,?_,?_,hm⟩,hxb,hg,hyb⟩
    · intro g j i
      have hh := hl.2.2.1 g j i
      simpa only [sourceOriginalMemoryFixedPhysicalChoice434,
        show (st.2 g).1=(X.2 g).1 from congrArg Prod.fst (hxb g),
        show (b g).1=(Y.2 g).1 from congrArg Prod.fst (hyb g)] using hh
    · constructor
      · intro g i hi
        exact (hm g).2 i hi
      · intro g i hi
        have hh := (hg g).shared_copy i hi
        simpa only [show (st.2 g).1=(X.2 g).1 from congrArg Prod.fst (hxb g),
          show (b g).1=(Y.2 g).1 from congrArg Prod.fst (hyb g)] using hh
  · rintro ⟨hxs,hzs,hh,hxb,hg,hyb⟩
    have hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X :=
      Prod.ext hxs (funext hxb)
    refine ⟨hx,⟨hh.1,hh.2.1,?_,?_,?_⟩,?_⟩
    · intro g j i
      have ha := hh.2.2.1 g j i
      simpa only [sourceOriginalMemoryFixedPhysicalChoice434,
        show (st.2 g).1=(X.2 g).1 from congrArg Prod.fst (hxb g),
        show (b g).1=(Y.2 g).1 from congrArg Prod.fst (hyb g)] using ha
    · simpa only [sourceOriginalMemoryFixedPhysicalChoice434,hd hx,hdelta hx,
        sourceOriginalMemoryBigFrameLegal434] using hg
    · simpa only [sourceOriginalMemoryFixedPhysicalChoice434,hdelta hx,hxs,hzs] using hh.2.2.2.2
    · apply Prod.ext hzs
      funext g
      simpa only [sourceOrientedPhysicalOutput,sourceOriginalMemoryFixedPhysicalChoice434,
        fullPhysicalBranchOutput,bigGroupBranchOutput,physicalBranchOutput,hdelta hx] using hyb g
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalPairPacket -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 32000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal original packet, disintegrated at two physical Fock
endpoints. Arbitrary joint K and both Fourier/Mellin phases remain in
the actual coefficient. -/
def sourceOriginalMemoryOriginalPairPacket434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
    ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
    ∑ zs : GroupState SP smallMod (J+ell),
      let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs
      if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

/-- Exact norm-kernel disintegration for the LITERAL original E packet.
K is evaluated once at the two full BIG endpoint arrays, after fixing
all physical endpoints. The formula neither assumes a separable K nor
changes the original harmonic/Fock mass or its multiplicities. -/
theorem source_original_memory_ORIGINAL_pair_packet434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalPairPacket434 SP smallMod BP bigMod J ell m cap patterns
      nu aux bs bt ss tt q rho Vs Vb mu Knu zeta theta o k X Y =
    sourceOriginalMemoryEnvelopeFramePair434 SP smallMod BP bigMod J ell m (patterns nu) cap
      aux bs bt ss tt q rho Vs Vb mu
      ‖Knu nu aux (fun g i => (X.2 g).1 (bs g i)) (fun g i => (Y.2 g).1 (bt g i))‖
      o k X Y := by
  classical
  let D := sourceOriginalMemoryOutputD434 SP smallMod BP bigMod J ell m (patterns nu) aux X bs ss
  let delta := o*k*(D:ℤ)
  let W := ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
    (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
    (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  let H := ‖Knu nu aux (fun g i => (X.2 g).1 (bs g i)) (fun g i => (Y.2 g).1 (bt g i))‖
  let sm := ‖groupPermutedKernel SP smallMod (J+ell) q Vs (sourceSmallShared J ell)
    delta (fun _ _ => 1) ss tt X.1 Y.1‖
  let A := W*H*sm
  let gate := sourceOriginalMemoryEnvelopePairGate434 SP smallMod BP bigMod J ell m
    (patterns nu) aux bs bt ss tt o k X Y
  let good := fun (xb : BigGroupState BP bigMod (J+ell) cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap xb) =>
    (∀ g,sourceOriginalMemoryBigProjection434 (bigMod g) (J+ell) (cap g) (xb g)=X.2 g) ∧
    sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap xb
      (sourceBigShared J ell m (patterns nu)) bs bt D delta b ∧
    (∀ g,((b g).1,physicalPendingMultiset (bigMod g) (J+ell) (cap g) (xb g)
      (bs g) delta (b g).2)=Y.2 g)
  let bn := fun (xb : BigGroupState BP bigMod (J+ell) cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap xb) =>
    sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap xb mu Vb rho
      (sourceBigShared J ell m (patterns nu)) bs bt delta b
  let br := fun xb => ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap xb,
    if good xb b then bn xb b else 0
  let choice := fun st => sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
    J ell m cap patterns nu aux st bs bt ss tt
  have ht (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2)
      (zs : GroupState SP smallMod (J+ell)) :
      (if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k (choice st b zs) ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k
          (choice st b zs)=Y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st (choice st b zs)‖ else 0) =
      if st.1=X.1 then if zs=Y.1 then
        if gate then A*(if good st.2 b then bn st.2 b else 0) else 0
        else 0 else 0 := by
    have he := source_original_memory_ORIGINAL_pair_legal434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bs bt ss tt b zs o k X Y
    by_cases hp : physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k (choice st b zs) ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k
          (choice st b zs)=Y
    · obtain ⟨hs,hzs,hg,hxb,hb,hyb⟩ := he.mp hp
      rw [if_pos hp,if_pos hs,if_pos hzs,if_pos hg,if_pos (show good st.2 b from ⟨hxb,hb,hyb⟩)]
      have hD : sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
          (patterns nu) aux st bs ss=D := by
        rw [← source_original_memory_ORIGINAL_input_D434 SP smallMod BP bigMod
          J ell m cap patterns nu aux st bs ss,hp.1]
      have hd : sourceOrientedStep SP smallMod BP bigMod J ell m cap
          (patterns nu) aux st bs ss o k=delta := by
        unfold sourceOrientedStep
        rw [hD]
      have hki : (fun g i => (st.2 g).1 (bs g i))=(fun g i => (X.2 g).1 (bs g i)) := by
        funext g i
        exact congrFun (congrArg Prod.fst (hxb g)) (bs g i)
      have hko : (fun g i => (b g).1 (bt g i))=(fun g i => (Y.2 g).1 (bt g i)) := by
        funext g i
        exact congrFun (congrArg Prod.fst (hyb g)) (bt g i)
      have hn := source_original_memory_ORIGINAL_coefficient_norm_factor434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt b zs q rho Vs Vb mu Knu
        zeta theta o k hp.2.1.1
      dsimp only at hn
      rw [hd,hki,hko,hs,hzs] at hn
      dsimp only [choice]
      rw [hzs]
      exact hn.trans (by dsimp only [A,W,H,sm,bn];ring)
    · rw [if_neg hp]
      split_ifs with hs hzs hg hb <;> try simp only [mul_zero]
      exact False.elim (hp (he.mpr ⟨hs,hzs,hg,hb.1,hb.2.1,hb.2.2⟩))
  unfold sourceOriginalMemoryOriginalPairPacket434 sourceOriginalMemoryEnvelopeFramePair434
  by_cases hg : gate
  · rw [if_pos hg]
    have hi (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
        (∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        ∑ zs : GroupState SP smallMod (J+ell),
          if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
            sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k
              (choice st b zs) ∧
            sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k
              (choice st b zs)=Y
          then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
            q rho Vs Vb mu Knu zeta theta o k st (choice st b zs)‖ else 0) =
        if st.1=X.1 then A*br st.2 else 0 := by
      simp_rw [ht,if_pos hg]
      by_cases hs : st.1=X.1
      · simp only [if_pos hs]
        simp [br,Finset.mul_sum]
      · simp [hs]
    rw [show (∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
      ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
      ∑ zs : GroupState SP smallMod (J+ell),
        let z := choice st b zs
        if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
          sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
          sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ else 0) =
      ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
          (if st.1=X.1 then A*br st.2 else 0) by
        apply Finset.sum_congr rfl
        intro st hst
        congr 1
        exact hi st]
    simp_rw [source_original_memory_FULL_density_mass_product434]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    let mb := fun (xb : BigGroupState BP bigMod (J+ell) cap) => ∏ g : BG,sourceOriginalMemoryBigDensityMass434 (bigMod g)
      (J+ell) (cap g) (mu g) (Vb g) (xb g)
    have hsum (xb : BigGroupState BP bigMod (J+ell) cap) :
        (∑ xs : GroupState SP smallMod (J+ell),
          (groupStateMass SP smallMod (J+ell) Vs * mb xb) *
          (if xs=X.1 then A*br xb else 0)) =
        (groupStateMass SP smallMod (J+ell) Vs * mb xb)*(A*br xb) := by
      simp only [mul_ite,mul_zero]
      simp
    change (∑ xb : BigGroupState BP bigMod (J+ell) cap,
      ∑ xs : GroupState SP smallMod (J+ell),
        (groupStateMass SP smallMod (J+ell) Vs * mb xb) *
          (if xs=X.1 then A*br xb else 0)) = _
    simp_rw [hsum]
    unfold sourceOriginalMemoryBigFrameDensityPair434
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xb hxb
    dsimp only [A,W,H,sm,mb,br,good,bn,D,delta]
    ring
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro st hst
    rw [show (∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
      ∑ zs : GroupState SP smallMod (J+ell),
        if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
          sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k (choice st b zs) ∧
          sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k (choice st b zs)=Y
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (choice st b zs)‖ else 0)=0 by
      simp_rw [ht,if_neg hg]
      simp]
    exact mul_zero _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalDensityPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 28000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Absolute coefficient kernel between two physical endpoints of the complete literal original E
under the auxiliary density. All nu, auxiliary, endpoint permutations,
physical states and legal branch witnesses remain in this finite sum. -/
def sourceOriginalMemoryOriginalDensityPair434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℝ :=
  ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
    ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if physicalFockProjection SP smallMod BP bigMod (J+ell) cap st=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=Y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

theorem source_original_memory_ORIGINAL_pair_packets434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k X Y =
    ∑ nu : Nu,∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
    ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryOriginalPairPacket434 SP smallMod BP bigMod J ell m cap
        patterns nu aux bs bt ss tt q rho Vs Vb mu Knu zeta theta o k X Y := by
  classical
  letI (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
      Fintype (sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) := inferInstance
  letI : Fintype (Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 ×
        GroupState SP smallMod (J+ell)) := inferInstance
  letI (nu : Nu) : Fintype (SourceBigAux BP J m (patterns nu)) := inferInstance
  let e :
      (Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) ≃
      (Σ nu : Nu,SourceBigAux BP J m (patterns nu) ×
        BigGroupPerm (BG:=BG) (J+ell) × BigGroupPerm (BG:=BG) (J+ell) ×
        GroupPermFamily (G:=SG) (J+ell) × GroupPermFamily (G:=SG) (J+ell) ×
        (Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
          sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 ×
            GroupState SP smallMod (J+ell))) :=
    { toFun := fun ⟨st,nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩ => ⟨nu,aux,bs,bt,ss,tt,st,b,zs⟩
      invFun := fun ⟨nu,aux,bs,bt,ss,tt,st,b,zs⟩ => ⟨st,nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩
      left_inv := by rintro ⟨st,nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩;rfl
      right_inv := by rintro ⟨nu,aux,bs,bt,ss,tt,st,b,zs⟩;rfl }
  let w := fun (z : Σ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) =>
    sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu z.1 *
      (if physicalFockProjection SP smallMod BP bigMod (J+ell) cap z.1=X ∧
        sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns z.1 o k z.2 ∧
        sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns z.1 o k z.2=Y
      then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k z.1 z.2‖ else 0)
  have he := Fintype.sum_equiv e w (fun z => w (e.symm z))
    (by intro z;rw [e.symm_apply_apply])
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,
    sourceOriginalMemoryOriginalDensityPair434,sourceOriginalMemoryOriginalPairPacket434,
    sourceOriginalMemoryFixedPhysicalChoice434,Finset.mul_sum,w,e,Equiv.coe_fn_symm_mk] at he ⊢
  convert he using 1 <;> congr <;> exact Subsingleton.elim _ _


/-- The absolute original packet reverses with the transposed JOINT K.
The Fourier/Mellin parameters are arbitrary and remain in the literal
coefficients on both sides. This is not an assertion about the signed
operator or an invariance of the original K under transposition. -/
theorem source_original_memory_ORIGINAL_pair_packet_reverse434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hmu : ∀ g p,0 < mu g p) (hVb : ∀ g,0<Vb g) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalPairPacket434 SP smallMod BP bigMod J ell m cap patterns
      nu aux bs bt ss tt q rho Vs Vb mu Knu zeta theta o k X Y =
    sourceOriginalMemoryOriginalPairPacket434 SP smallMod BP bigMod J ell m cap patterns
      nu aux bt bs tt ss q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s)
        zeta theta (-o) k Y X := by
  rw [source_original_memory_ORIGINAL_pair_packet434,
    source_original_memory_ORIGINAL_pair_packet434]
  exact source_original_memory_ENVELOPE_frame_pair_reverse434 SP smallMod BP bigMod
    J ell m (patterns nu) cap aux bs bt ss tt q rho Vs Vb mu hmu hVb hr _ o k X Y

/-- Exact weighted detailed balance for the COMPLETE original absolute
kernel. All nu, auxiliary labels, both endpoint permutation families
and every physical Fock sector remain inside the literal carrier.
The joint comparison multiplier is transposed, not factorized. -/
theorem source_original_memory_ORIGINAL_density_pair_reverse434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hmu : ∀ g p,0 < mu g p) (hVb : ∀ g,0<Vb g) (hr : 0 ≤ rho)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (X Y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k X Y =
    sourceOriginalMemoryOriginalDensityPair434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu (fun nu aux s t => Knu nu aux t s) zeta theta (-o) k Y X := by
  classical
  rw [source_original_memory_ORIGINAL_pair_packets434,
    source_original_memory_ORIGINAL_pair_packets434]
  apply Finset.sum_congr rfl
  intro nu hnu
  apply Finset.sum_congr rfl
  intro aux haux
  simp_rw [source_original_memory_ORIGINAL_pair_packet_reverse434 SP smallMod BP bigMod
    J ell m cap patterns nu aux _ _ _ _ q rho Vs Vb mu hmu hVb hr Knu zeta theta o k X Y]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bt hbt
  apply Finset.sum_congr rfl
  intro bs hbs
  exact Finset.sum_comm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalOriginalEColumn -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Complete column exponent: the already explicit SMALL/nu losses,
plus the fixed BIG row exponent. It is independent of J and L. -/
def sourceOriginalMemoryEColumnLoss434
    (cfg : SourceComparisonFixed434) (ell Cq Cxi : ℕ) (q rho : ℝ) : ℝ :=
  sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q +
    cfg.C0*Real.log (sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax))

/-- Applicable polynomial column bound for the COMPLETE original
RAW plus canonical signed two-block Knu family, with the true muTilde
and the exact original output and orbit normalization. The eventual
threshold precedes J, every growing group/prime carrier and every OLD
cutoff. No pointwise K cap or operator premise remains to be supplied. -/
theorem eventually_source_original_memory_PHYSICAL_ORIGINAL_E_density_column434
    (cfg : SourceComparisonFixed434) (ell Cq Cxi : ℕ)
    (q rho : ℝ) (hq : 0<q) (hq1 : q<1) (hr : 0< rho) (hr1 : rho<1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (J m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ)
      (y : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell)),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalMemoryOriginalDensityColumn434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho data.Vsmall data.Vbig mu
      (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q hA hB xi) zeta theta o k y ≤
    L^(sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho) *
      (physicalOrbitMass
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        (J+ell) cap data.Vsmall mu y *
      sourceOriginalMemorySectorDensity434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell data.Vbig y) := by
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data instS instB
    J m hm hmJ cap hBigLower hHarmonic blockA blockB hBlocks Q xi hxi hQ hXi
    hA hB hhA hhB zeta theta o k y
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hLp : 0<L := zero_lt_one.trans_le hL1
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) (hb g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hMass (g : G) : ∑ p : BP g,mu g p ≤ 2 :=
    (source_original_memory_physical_tilt_mass_two434 BP (fun _ p => p.val)
      q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig g (hVb g) (hHarmonic g) (hb g)).2
  let Cs := sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) cfg.vmin cfg.C0
  let C1 : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let Cb := cfg.C0*Real.log (sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax))
  have hBlocksCap : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hh : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (show (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) by exact_mod_cast hh).trans
      data.hBigGroups
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
  have hmem (d : ℕ) : 0 ≤ memoryPromotionDampingConstant rho d := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hBig :
      (∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
        ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m)))) ≤ L^Cb := by
    apply le_trans _ (source_original_memory_BIG_row_factor_polynomial434
      rho cfg.vmin 2 cfg.C0 L (ell+cfg.tmax) hr hr1 cfg.hv (by norm_num) hL1
      data.Vbig data.hVbig data.hBigGroups)
    apply Finset.prod_le_prod₀
    · intro g hg
      have hh := hmem (ell+m)
      positivity
    · intro g hg
      exact source_original_memory_complete_row_factor_mono434 rho (data.Vbig g) 2 hr1
        (by norm_num) (ell+m) (ell+cfg.tmax) (Nat.add_le_add_left hm ell)
  have hSmall0 : 0 ≤ ∏ g : ι,memorySmallRowConstant q (data.Vsmall g) ell := by
    have hs : 0<1-Real.sqrt q := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hBig0 : 0 ≤ ∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
      ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m))) := by
    apply Finset.prod_nonneg
    intro g hg
    have hh := hmem (ell+m)
    positivity
  have hOrbit0 : 0 ≤ physicalOrbitMass
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      BP (fun _ p => p.val) (J+ell) cap data.Vsmall mu y := by
    unfold physicalOrbitMass
    apply Finset.sum_nonneg
    intro st hst
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun g _ =>
        (stateMass_positive (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
          (J+ell) (data.Vsmall g) (hVs g)).le)
    · exact (bigGroupStateMass_positive BP (fun _ p => p.val) (J+ell) cap mu hmu st.2).le
  have hDensity0 := (source_original_memory_sector_density_pos434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell data.Vbig hVb y).le
  have hColumn := source_original_memory_ORIGINAL_E_density_column434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell m cap
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho 2 data.Vsmall data.Vbig mu hq hq1 hr hr1 hVs hVb hmu
    (by norm_num) hMass hHarmonic
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi)
    zeta theta o k (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
    (source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi hhA hhB hxi) y
  apply hColumn.trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hOrbit0 hDensity0)
  calc
    _ ≤ (L^C1*L^Cs)*L^Cb :=
      mul_le_mul (mul_le_mul hKsum hSmall hSmall0 (Real.rpow_nonneg hLp.le _))
        hBig hBig0 (mul_nonneg (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _))
    _ = _ := by
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      dsimp only [sourceOriginalMemoryEColumnLoss434,sourceOriginalMemoryERowLoss434,Cs,C1,Cb]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalPromotionL2 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 28000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_memory_ORIGINAL_legal_output_mem434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z) :
    sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z ∈
      physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨sourceOriginalMemoryActualOrderedOutput434 SP smallMod BP bigMod J ell m cap
    patterns st o k z hz,Finset.mem_univ _,?_⟩
  simp only [physicalFockProjection,sourceOriginalMemoryActualOrderedOutput434,
    sourceOrientedPhysicalOutput,fullPhysicalBranchOutput,bigGroupBranchOutput,
    physicalBranchOutput,Green64Fock.fockMultiset,physicalPendingMultiset,List.ofFn_get]
  rfl

/-- A weighted Cauchy bound for the literal signed promotion part,
against the squared observable at the actual physical output. -/
theorem source_original_memory_ORIGINAL_promotion_row_energy434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    ‖sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st F‖^2 ≤
    sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st *
    ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z then
        ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ *
        ‖F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)‖^2
      else 0 := by
  classical
  let a := fun z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st =>
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      (∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ else 0
  let f := fun z => F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)
  have ha (z) : 0 ≤ a z := by dsimp only [a];split_ifs <;> positivity
  have ht :
      ‖sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st F‖ ≤ ∑ z,a z*‖f z‖ := by
    unfold sourceOriginalMemoryOriginalEPromotion434 sourceOrientedPhysicalChoices
    rw [Finset.sum_filter]
    apply le_trans (norm_sum_le _ _) (le_of_eq _)
    apply Finset.sum_congr rfl
    intro z hz
    dsimp only [a,f]
    by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
    · by_cases hp : ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty
      · simp only [hl,hp,ite_true,and_self,norm_mul]
      · simp only [hl,hp,ite_true,ite_false,and_false,norm_zero,zero_mul]
    · simp only [hl,ite_false,false_and,norm_zero,zero_mul]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s:=Finset.univ) (r:=fun z => a z*‖f z‖)
    (f:=a) (g:=fun z => a z*‖f z‖^2)
    (fun z _ => ha z) (fun z _ => mul_nonneg (ha z) (sq_nonneg _))
    (fun z _ => by ring_nf;exact le_rfl)
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun z _ => ha z))
  apply Finset.sum_le_sum
  intro z hz
  dsimp only [a,f]
  split_ifs <;> (try simp only [zero_mul]) <;> first | exact le_rfl | positivity | tauto

/-- Exact output-fibre organization of the complete original absolute
energy sum. The output support is the actual physical Fock support. -/
theorem source_original_memory_ORIGINAL_column_energy_fibres434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    (∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
      ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
        if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z then
          ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
            q rho Vs Vb mu Knu zeta theta o k st z‖ *
          ‖F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)‖^2
        else 0) =
    ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap
        patterns q rho Vs Vb mu Knu zeta theta o k y * ‖F y‖^2 := by
  classical
  have he (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) :
      (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z then
        ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ *
        ‖F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)‖^2
      else 0) =
      ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
          sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z=y
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ else 0)*‖F y‖^2 := by
    by_cases hl : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
    · have hm := source_original_memory_ORIGINAL_legal_output_mem434 SP smallMod BP bigMod
        J ell m cap patterns st o k z hl
      simp only [hl,ite_true,true_and,ite_mul,zero_mul]
      rw [Finset.sum_eq_single
        (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)]
      · simp
      · intro b hb hne
        exact if_neg (Ne.symm hne)
      · intro hnot
        exact False.elim (hnot hm)
    · simp only [hl,ite_false,false_and,zero_mul,Finset.sum_const_zero]
  simp_rw [he]
  unfold sourceOriginalMemoryOriginalDensityColumn434
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2;ext st
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro st hst
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- The actual promotion operator satisfies the weighted two-sided
bound once its literal rows and the complete literal columns are
bounded. The physical theorem discharges both premises separately. -/
theorem source_original_memory_ORIGINAL_promotion_L2_transfer434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (eligible : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → Prop)
    (R C : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ st,eligible st →
      sourceOriginalMemoryOriginalEPromotionRow434 SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st ≤ R)
    (hcol : ∀ y,sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap
      patterns q rho Vs Vb mu Knu zeta theta o k y ≤
      C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    (∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      if eligible st then
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
        ‖sourceOriginalMemoryOriginalEPromotion434 SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st F‖^2 else 0) ≤
    R*C*(∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y)*‖F y‖^2) := by
  classical
  let e := fun st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap =>
    ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
      if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z then
        ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st z‖ *
        ‖F (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z)‖^2
      else 0
  have he0 (st) : 0 ≤ e st := Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  calc
    _ ≤ R*(∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st*e st) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro st hst
      have hw := source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
        J ell cap Vs Vb mu hVs hVb hmu st
      by_cases hs : eligible st
      · rw [if_pos hs]
        have hh := (source_original_memory_ORIGINAL_promotion_row_energy434 SP smallMod BP bigMod
          J ell m cap patterns q rho Vs Vb mu Knu zeta theta o k st F).trans
          (mul_le_mul_of_nonneg_right (hrow st hs) (he0 st))
        exact (mul_le_mul_of_nonneg_left hh hw).trans_eq (by ring)
      · rw [if_neg hs]
        exact mul_nonneg hR (mul_nonneg hw (he0 st))
    _ = R*(∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        sourceOriginalMemoryOriginalDensityColumn434 SP smallMod BP bigMod J ell m cap
          patterns q rho Vs Vb mu Knu zeta theta o k y*‖F y‖^2) := by
      rw [source_original_memory_ORIGINAL_column_energy_fibres434]
    _ ≤ R*(∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        (C*(physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
          sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y))*‖F y‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y hy =>
        mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _))) hR
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalOriginalEPromotionL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- Explicit compatible budget for the promotion L2 estimate. The
column loss is fixed before J; increasing J does not increase that loss. -/
theorem source_original_memory_PROMOTION_L2_parameter_budget434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (q rho c0 B : ℝ) (hc0 : 0<c0) :
    let E := sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let C := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K (2*B+C+E)
    max Jmin cfg.tmax ≤ J ∧
      2*B+2*E+2*cfg.C0*Real.log K+3 ≤
        c0*Real.log (((J+ell).choose ell:ℕ):ℝ) := by
  dsimp only
  have hh := source_original_memory_rare_slot_choice434 (max Jmin cfg.tmax) ell hell
    c0 cfg.C0 (sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax))
    (2*B+sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho+
      sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q) hc0
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1 <;>
    dsimp only [sourceOriginalMemoryEColumnLoss434] <;> ring

/-- Applicable logarithmically small L2 estimate for the literal signed
promotion part of original E, on source states with TOTAL OLD≤ ceil L².
It uses the original RAW+canonical Knu, both Fourier/Mellin parameters,
both endpoint permutations and the true harmonic/Fock coefficients.
The auxiliary density changes neither the orbit-compressed row nor
the vacuum root. No small row, column, Gram or operator premise remains.
The store-only part and the full marked G/Memory chain are not asserted. -/
theorem source_original_memory_PHYSICAL_ORIGINAL_E_promotion_L2_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let Brow := 2*B+Ccol
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (Brow+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (F : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → ℂ),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    (∑ st : FullPhysicalState
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
      if (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) then
        sourceOriginalMemoryFullDensityMass434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell cap data.Vsmall data.Vbig mu st *
        ‖sourceOriginalMemoryOriginalEPromotion434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          q rho data.Vsmall data.Vbig mu
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
            J ell m hmJ Q hA hB xi) zeta theta o k st F‖^2 else 0) ≤
    L^(-(2*B)) *
      (∑ y ∈ physicalFockOrbitSupport
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
        (physicalOrbitMass
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          (J+ell) cap data.Vsmall mu y *
        sourceOriginalMemorySectorDensity434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell data.Vbig y)*‖F y‖^2) := by
  dsimp only
  let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
  let Brow := 2*B+Ccol
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (Brow+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
  have hRow := source_original_memory_PHYSICAL_ORIGINAL_E_promotion_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 Brow hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hRow.1,?_⟩
  filter_upwards [hRow.2,
    eventually_source_original_memory_PHYSICAL_ORIGINAL_E_density_column434 cfg ell Cq Cxi
      q rho hq hq1 hr hr1,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hrow hcol hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower blockA blockB hBlocks
    Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk F
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hh := source_original_memory_ORIGINAL_promotion_L2_transfer434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell m cap
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho data.Vsmall data.Vbig mu hVs hVb hmu
    (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi)
    zeta theta o k
    (fun st => (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2))
    (L^(-Brow)) (L^Ccol) (Real.rpow_nonneg hLp.le _)
    (fun st hOld => hrow x Y Hprime data sep m hm hmJ cap st hSmallUpper hBigLower
      hHarmonic hSmallGroupsLower hOld blockA blockB hBlocks Q xi hxi hQ hXi
      hA hB hhA hhB zeta theta o k ho hk0 hk)
    (fun y => hcol x Y Hprime data J m hm hmJ cap hBigLower hHarmonic
      blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k y) F
  rw [← Real.rpow_add hLp] at hh
  rw [show -Brow+Ccol= -(2*B) by dsimp only [Brow];ring] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro st hst
  by_cases he : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2)
  · simp only [he,ite_true]
    congr <;> exact Subsingleton.elim _ _
  · simp only [he,ite_false]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOrbitDensityL2 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The actual physical Fock orbit average is a contraction in the
auxiliary V-power density. Zero-mass fibres are included, and no
counting measure or sector cardinality replaces the original mass. -/
theorem source_original_memory_ORIGINAL_orbit_density_L2_contraction434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g) (hmu : ∀ g p,0 < mu g p)
    (F : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ) :
    (∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y) *
      ‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu F y‖^2) ≤
    ∑ st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu st *
      ‖F st‖^2 := by
  classical
  letI : DecidableEq (FullPhysicalOutput SP smallMod BP bigMod (J+ell)) := Classical.decEq _
  let project := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
  let w := sourceOriginalMemoryFullDensityMass434 SP smallMod BP bigMod J ell cap Vs Vb mu
  let M := fun y => physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vs mu y *
    sourceOriginalMemorySectorDensity434 SP smallMod BP bigMod J ell Vb y
  have hw (st) : 0 ≤ w st :=
    source_original_memory_FULL_density_mass_nonneg434 SP smallMod BP bigMod
      J ell cap Vs Vb mu hVs hVb hmu st
  have hmass (y) : (∑ st,if project st=y then w st else 0)=M y := by
    simpa only [Finset.sum_filter,sourceOriginalMemoryFullDensityMass434,w,project,M] using
      source_original_memory_sector_density_orbit_mass434 SP smallMod BP bigMod
        J ell cap Vs Vb mu y
  have hm (y) : 0 ≤ M y := by
    rw [← hmass]
    exact Finset.sum_nonneg (fun st _ => by split_ifs <;> first | exact hw st | exact le_rfl)
  have hterm (y) :
      M y*‖fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu F y‖^2 ≤
      ∑ st,if project st=y then w st*‖F st‖^2 else 0 := by
    rw [← source_original_memory_sector_density_orbit_average434
      SP smallMod BP bigMod J ell cap Vs Vb hVb mu F y]
    have hf := source_original_finite_selected_coefficient_fibre_L2_434 project w hw F y
    rw [hmass] at hf
    have ha :
        sourceOriginalMemoryDensityOrbitAverage434 SP smallMod BP bigMod J ell cap Vs Vb mu F y =
        sourceOriginalFiniteSelectedComplexCoefficient434 project w F y / (M y:ℂ) := by
      simp only [sourceOriginalMemoryDensityOrbitAverage434,
        sourceOriginalFiniteSelectedComplexCoefficient434,Finset.sum_filter,
        sourceOriginalMemoryFullDensityMass434,w,project,M]
    rw [ha]
    by_cases hz : M y=0
    · rw [hz,zero_mul]
      exact Finset.sum_nonneg (fun st _ => by
        split_ifs <;> first | exact mul_nonneg (hw st) (sq_nonneg _) | exact le_rfl)
    · have hp : 0<M y := lt_of_le_of_ne (hm y) (Ne.symm hz)
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
      calc
        _ = ‖sourceOriginalFiniteSelectedComplexCoefficient434 project w F y‖^2 / M y := by
          field_simp
        _ ≤ _ := (div_le_iff₀ hp).mpr (hf.trans_eq (mul_comm _ _))
  calc
    _ ≤ ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
        ∑ st,if project st=y then w st*‖F st‖^2 else 0 :=
      Finset.sum_le_sum (fun y _ => hterm y)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro st hst
      have hmemb : project st ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap :=
        Finset.mem_image.mpr ⟨st,Finset.mem_univ _,rfl⟩
      rw [Finset.sum_eq_single (project st)]
      · simp [w]
      · intro y hy hne
        exact if_neg (Ne.symm hne)
      · exact fun hnot => False.elim (hnot hmemb)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalCompressedPromotionL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- Applicable promotion saving after the ORIGINAL physical Fock orbit
compression. The source TOTAL OLD projection remains explicit. All
moving data and full joint output observables are uniformly quantified.
This theorem does not assert the marked-history or store-only bounds. -/
theorem source_original_memory_PHYSICAL_ORIGINAL_E_compressed_promotion_L2_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let Brow := 2*B+Ccol
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (Brow+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (F : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → ℂ),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    (∑ y ∈ physicalFockOrbitSupport
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
      (physicalOrbitMass (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap data.Vsmall mu y *
        sourceOriginalMemorySectorDensity434 (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) J ell data.Vbig y) *
      ‖fullPhysicalOrbitAverage (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap data.Vsmall mu
        (fun st => if (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) then
        sourceOriginalMemoryOriginalEPromotion434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          q rho data.Vsmall data.Vbig mu
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
            J ell m hmJ Q hA hB xi) zeta theta o k st F else 0) y‖^2) ≤
    L^(-(2*B)) *
      (∑ y ∈ physicalFockOrbitSupport
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
        (physicalOrbitMass
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          (J+ell) cap data.Vsmall mu y *
        sourceOriginalMemorySectorDensity434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell data.Vbig y)*‖F y‖^2) := by
  dsimp only
  let Ccol := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
  let Brow := 2*B+Ccol
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (Brow+sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q)
  have hRow := source_original_memory_PHYSICAL_ORIGINAL_E_promotion_L2_log_saving434
    cfg ell Jmin Cq Cxi hell Ck q rho c0 B hq hq1 hr hr1 hc0
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨hRow.1,?_⟩
  filter_upwards [hRow.2,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hrow hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower blockA blockB hBlocks
    Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk F
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hh := hrow x Y Hprime data sep m hm hmJ cap hSmallUpper hBigLower
    hHarmonic hSmallGroupsLower blockA blockB hBlocks Q xi hxi hQ hXi
    hA hB hhA hhB zeta theta o k ho hk0 hk F
  have ha := source_original_memory_ORIGINAL_orbit_density_L2_contraction434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) J ell cap data.Vsmall data.Vbig mu hVs hVb hmu
    (fun st => if (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) then
        sourceOriginalMemoryOriginalEPromotion434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          q rho data.Vsmall data.Vbig mu
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
            J ell m hmJ Q hA hB xi) zeta theta o k st F else 0)
  have ha' :
    (∑ y ∈ physicalFockOrbitSupport
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
      (physicalOrbitMass (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap data.Vsmall mu y *
        sourceOriginalMemorySectorDensity434 (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) J ell data.Vbig y) *
      ‖fullPhysicalOrbitAverage (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap data.Vsmall mu
        (fun st => if (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) then
        sourceOriginalMemoryOriginalEPromotion434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          q rho data.Vsmall data.Vbig mu
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
            J ell m hmJ Q hA hB xi) zeta theta o k st F else 0) y‖^2) ≤
    (∑ st : FullPhysicalState
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap,
      if (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) then
        sourceOriginalMemoryFullDensityMass434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell cap data.Vsmall data.Vbig mu st *
        ‖sourceOriginalMemoryOriginalEPromotion434
          (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
          J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          q rho data.Vsmall data.Vbig mu
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
            J ell m hmJ Q hA hB xi) zeta theta o k st F‖^2 else 0) := by
    convert ha using 1
    apply Finset.sum_congr rfl
    intro st hst
    by_cases he : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2)
    · simp only [he,ite_true]
    · simp [he]
  exact ha'.trans hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalTransposeColumn -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Applicable polynomial column bound for the COMPLETE transposed original
RAW plus canonical signed two-block Knu family, with the true muTilde
and the exact original output and orbit normalization. The eventual
threshold precedes J, every growing group/prime carrier and every OLD
cutoff. No pointwise K cap or operator premise remains to be supplied. -/
theorem eventually_source_original_memory_PHYSICAL_TRANSPOSE_E_density_column434
    (cfg : SourceComparisonFixed434) (ell Cq Cxi : ℕ)
    (q rho : ℝ) (hq : 0<q) (hq1 : q<1) (hr : 0< rho) (hr1 : rho<1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (J m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ)
      (y : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell)),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalMemoryOriginalDensityColumn434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho data.Vsmall data.Vbig mu
      (fun nu aux s t => sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q hA hB xi nu aux t s) zeta theta o k y ≤
    L^(sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho) *
      (physicalOrbitMass
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        (J+ell) cap data.Vsmall mu y *
      sourceOriginalMemorySectorDensity434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell data.Vbig y) := by
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data instS instB
    J m hm hmJ cap hBigLower hHarmonic blockA blockB hBlocks Q xi hxi hQ hXi
    hA hB hhA hhB zeta theta o k y
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hLp : 0<L := zero_lt_one.trans_le hL1
  have hVs : ∀ g,0<data.Vsmall g := fun g => cfg.hv.trans_le (data.hVsmall g)
  have hVb : ∀ g,0<data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le _ g p (hVisit p.val (hBigLower g p.val p.property))).1
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0<(p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb0 : 0<physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) (hb g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hMass (g : G) : ∑ p : BP g,mu g p ≤ 2 :=
    (source_original_memory_physical_tilt_mass_two434 BP (fun _ p => p.val)
      q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig g (hVb g) (hHarmonic g) (hb g)).2
  let Cs := sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) cfg.vmin cfg.C0
  let C1 : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let Cb := cfg.C0*Real.log (sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax))
  have hBlocksCap : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hh : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (show (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) by exact_mod_cast hh).trans
      data.hBigGroups
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
  have hmem (d : ℕ) : 0 ≤ memoryPromotionDampingConstant rho d := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hBig :
      (∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
        ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m)))) ≤ L^Cb := by
    apply le_trans _ (source_original_memory_BIG_row_factor_polynomial434
      rho cfg.vmin 2 cfg.C0 L (ell+cfg.tmax) hr hr1 cfg.hv (by norm_num) hL1
      data.Vbig data.hVbig data.hBigGroups)
    apply Finset.prod_le_prod₀
    · intro g hg
      have hh := hmem (ell+m)
      positivity
    · intro g hg
      exact source_original_memory_complete_row_factor_mono434 rho (data.Vbig g) 2 hr1
        (by norm_num) (ell+m) (ell+cfg.tmax) (Nat.add_le_add_left hm ell)
  have hSmall0 : 0 ≤ ∏ g : ι,memorySmallRowConstant q (data.Vsmall g) ell := by
    have hs : 0<1-Real.sqrt q := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hBig0 : 0 ≤ ∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
      ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m))) := by
    apply Finset.prod_nonneg
    intro g hg
    have hh := hmem (ell+m)
    positivity
  have hOrbit0 : 0 ≤ physicalOrbitMass
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
      BP (fun _ p => p.val) (J+ell) cap data.Vsmall mu y := by
    unfold physicalOrbitMass
    apply Finset.sum_nonneg
    intro st hst
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun g _ =>
        (stateMass_positive (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
          (J+ell) (data.Vsmall g) (hVs g)).le)
    · exact (bigGroupStateMass_positive BP (fun _ p => p.val) (J+ell) cap mu hmu st.2).le
  have hDensity0 := (source_original_memory_sector_density_pos434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell data.Vbig hVb y).le
  have hColumn := source_original_memory_ORIGINAL_E_density_column434
    (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
    BP (fun _ p => p.val) J ell m cap
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q rho 2 data.Vsmall data.Vbig mu hq hq1 hr hr1 hVs hVb hmu
    (by norm_num) hMass hHarmonic
    (fun nu aux s t => sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q hA hB xi nu aux t s)
    zeta theta o k (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
    (fun nu aux s t => source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q hA hB xi hhA hhB hxi nu aux t s) y
  apply hColumn.trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hOrbit0 hDensity0)
  calc
    _ ≤ (L^C1*L^Cs)*L^Cb :=
      mul_le_mul (mul_le_mul hKsum hSmall hSmall0 (Real.rpow_nonneg hLp.le _))
        hBig hBig0 (mul_nonneg (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _))
    _ = _ := by
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      dsimp only [sourceOriginalMemoryEColumnLoss434,sourceOriginalMemoryERowLoss434,Cs,C1,Cb]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryProjectedDirtyBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Explicit compatible fixed budget for signed projected DIRTY:
one extra unit in the target saving absorbs the exact two-component
square loss at L≥2. Neither K nor E grows with J. -/
theorem source_original_memory_PROJECTED_DIRTY_parameter_budget434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (q rho c0 B : ℝ) (hc0 : 0<c0) :
    let E := sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let C := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (2*(B+1)+C+E)
    max Jmin cfg.tmax ≤ J ∧
      2*B+2*E+2*cfg.C0*Real.log K+5 ≤ c0*Real.log (((J+ell).choose ell:ℕ):ℝ) := by
  have h := source_original_memory_PROMOTION_L2_parameter_budget434 cfg ell Jmin Cq Cxi hell
    q rho c0 (B+1) hc0
  dsimp only at h ⊢
  refine ⟨h.1,?_⟩
  convert h.2 using 1 <;> ring

/-- The actual J is the following concrete integer, not an existential
choice postponed until after the moving family. -/
theorem source_original_memory_PROJECTED_DIRTY_explicit_J434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (q rho c0 B : ℝ) :
    let E := sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi q
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let C := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi q rho
    sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
      (2*(B+1)+C+E) =
    max (max Jmin cfg.tmax) (Nat.ceil
      (Real.exp ((2*B+2*E+2*cfg.C0*Real.log K+5)/c0))) := by
  dsimp only
  unfold sourceOriginalMemoryRareSlotChoice434
  congr 1
  apply congrArg (fun a : ℝ => Nat.ceil (Real.exp (a/c0)))
  unfold sourceOriginalMemoryEColumnLoss434
  ring

/-- A concrete admissible pair of damping parameters, including the
strict compatibility inequality needed by the pending marked-G work.
This witness does not assert free rho smallness for the vacuum root. -/
theorem source_original_memory_PROJECTED_DIRTY_nonempty_q_rho434 :
    0 < (1/4:ℝ) ∧ (1/4:ℝ)<1 ∧
    0 < Real.sqrt (3/4:ℝ) ∧ Real.sqrt (3/4:ℝ)<1 ∧
    Real.sqrt (1/4:ℝ) < (Real.sqrt (3/4:ℝ))^2 := by
  have hr0 : 0<Real.sqrt (3/4:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hrr := Real.sq_sqrt (by norm_num : 0 ≤ (3/4:ℝ))
  have hqq := Real.sq_sqrt (by norm_num : 0 ≤ (1/4:ℝ))
  refine ⟨by norm_num,by norm_num,hr0,?_,?_⟩
  · nlinarith only [hr0,hrr]
  · nlinarith only [hqq,hrr]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryStoreOnlyOldMonotonicity -/

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
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The exact TOTAL OLD count at the literal original physical output. -/
theorem source_original_memory_ORIGINAL_output_OLD_count434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st) :
    (∑ g : BG,
      ((sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z).2 g).2.card) =
    ∑ g : BG,((st.2 g).2.1.val - ((z.2.2.1.bigChoice g).2).2.1.card +
      ((z.2.2.1.bigChoice g).2).1.card) := by
  apply Finset.sum_congr rfl
  intro g hg
  change (physicalPendingOutput (bigMod g) (J+ell) (cap g) (st.2 g) _ _ _).length = _
  exact pending_output_length _ _ _ _ _ _ _

/-- With no promotion the exact increase is the number of stored slots. -/
theorem source_original_memory_ORIGINAL_no_promotion_OLD_count434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hnp : ¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty) :
    (∑ g : BG,
      ((sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z).2 g).2.card) =
    (∑ g : BG,(st.2 g).2.1.val) +
      ∑ g : BG,((z.2.2.1.bigChoice g).2).1.card := by
  have hp (g : BG) : ((z.2.2.1.bigChoice g).2).2.1=∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (fun h => hnp ⟨g,h⟩)
  rw [source_original_memory_ORIGINAL_output_OLD_count434]
  simp only [hp,Finset.card_empty,Nat.sub_zero,Finset.sum_add_distrib]

/-- Every literal store-only branch strictly increases TOTAL OLD.
This exact support fact suggests a reversed promotion estimate, but is
not itself a store-only norm bound. -/
theorem source_original_memory_ORIGINAL_store_only_OLD_strict434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hnp : ¬ ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty)
    (hs : ∃ g : BG,((z.2.2.1.bigChoice g).2).1.Nonempty) :
    (∑ g : BG,(st.2 g).2.1.val) <
    ∑ g : BG,
      ((sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z).2 g).2.card := by
  rw [source_original_memory_ORIGINAL_no_promotion_OLD_count434
    SP smallMod BP bigMod J ell m cap patterns st o k z hnp]
  obtain ⟨g,hg⟩ := hs
  have hp := Finset.card_pos.mpr hg
  have hl := Finset.single_le_sum
    (f:=fun g : BG => ((z.2.2.1.bigChoice g).2).1.card)
    (fun g _ => Nat.zero_le _) (Finset.mem_univ g)
  omega

/-- A strict decrease of TOTAL OLD can occur only in the actual
promotion component. No converse or per-history smallness is asserted. -/
theorem source_original_memory_ORIGINAL_OLD_decrease_has_promotion434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hd : (∑ g : BG,
      ((sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z).2 g).2.card) <
      ∑ g : BG,(st.2 g).2.1.val) :
    ∃ g : BG,((z.2.2.1.bigChoice g).2).2.1.Nonempty := by
  by_contra hn
  rw [source_original_memory_ORIGINAL_no_promotion_OLD_count434
    SP smallMod BP bigMod J ell m cap patterns st o k z hn] at hd
  omega
end Green64Analytic.CorrelationSquare

end

end

