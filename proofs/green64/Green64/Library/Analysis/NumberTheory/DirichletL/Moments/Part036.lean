module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part017
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part024
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part020
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part036

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def plainProfile (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (j:ℕ)(σ t:ℝ):ℝ→ℂ:=
  twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
    (orientedFrequency F.reverse t)

def slotWindow (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)(x:ℝ):ℂ:=
  conj (F.profile s x*(x:ℂ)^(F.external s-1))

def fiberPool (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot):
    Finset (CenteredMomentAddedZeroUniform.Tuple selected):=
  completePool (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (9/4) (9/4) (U^F.m) (U^F.m)

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ):Ideal O→ℂ:=
  finiteColumnCoefficient (fiberPool F selected)
    (uncenteredProfileCoefficient 1 (fun _:selected=>idealCoeff η.inverse)
      (fun s:selected=>slotWindow F s.val) (fun s:selected=>U^(F.widths s.val))
      (plainProfile F j σ t) (plainProfile F k σ t) (U^F.m) (U^F.m) 1 1 1)

def fiberSourceEnergy (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy (fun _=>True) (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem detector_row_eq_source (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(u:FreeRow)(hU:0<U):
    detectorPositiveRow F η selected j k σ t u=
      (Real.sqrt ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):ℂ)⁻¹*
      ∑I∈finiteColumns (fiberPool F selected),fiberCoefficient F η selected j k σ t I*
        CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I:=by
  have he:=positiveSlotRow_eq_complete_source η fixedBadMask 1 u.val 0
    (dvd_mul_right _ _) (dvd_mul_left _ _)
    (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1)] at he
  unfold detectorPositiveRow
  rw [rowMaskElement_eq_fixed]
  exact he

theorem detector_positive_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=>fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted (fun _ : O=>True) Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by simp) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le

theorem fiber_plain_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  exact detector_positive_energy_le_source Φ hΦ hone F η selected j k σ t hU

def radialMajorant : 𝓢(ℝ,ℂ):=
  Classical.choose DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant

lemma radialMajorant_compact : HasCompactSupport (radialMajorant:ℝ→ℂ):=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).1

lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x

lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx

theorem actual_fiber_plain_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t radialMajorant:=
  fiber_plain_energy_le_source radialMajorant radialMajorant_nonneg radialMajorant_one
    F η hdata hMm hU selected j k σ t hη

theorem actual_fiber_unmarked_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (j k:ℕ)(σ t:ℝ):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t‖^2)≤fiberSourceEnergy F η ∅ j k σ t radialMajorant:=by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    actual_fiber_plain_energy_le_source F η hdata hMm hU ∅ j k σ t (by simp)

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceBatch -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open ProbeHighRowFamily HeckeDetectorDyadicProfiles CenteredMomentPrimeSlot HeckeDetectorRowwisePolynomial
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem eventually_source_batch_plain_sectors {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hM : M=∏P∈S,P)
    (η : Character) (ell : Fin N→ℝ) (hell : ∀s,0<ell s)
    (W : Fin N→ℝ→ℂ) (hW : ∀s,Function.support (W s)⊆Set.Ici 1) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N) (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→B.profile=W→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin N),∀j k : ℕ,∀σ t : ℝ,
      let F:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase M H hH S hS η label
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^F.m) σ t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^F.m) σ t*
          F.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
          ∑u∈F.rows,‖fiberSector hH F η₀ selected j k σ t θ u‖^2 := by
  have hMm : M≤Ideal.span {rowMaskElement} := by
    rw [hM]
    exact source_product_le_rowMask S hbad
  filter_upwards [eventually_source_slots_coprime M H hH S hS η ell hell 1 (by norm_num),
    eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro d hd a ε tstar T allowance i B hdata hwidth hprofile bin label J K hne selected j k σ t
  dsimp only
  convert fiber_plain_sector_energy hH (B.fiber bin label J K hne)
    (sourceMomentBase M H hH S hS η label) ?_ hMm (Real.rpow_pos_of_pos hZ _) selected j k σ t ?_ using 1
  · congr 2 ; apply Subsingleton.elim
  · change B.data label=momentData (sourceMomentBase M H hH S hS η label)
    rw [hdata,sourceMomentData_base]
  · intro s hs P hP hp
    change P∈primePool M H (B.upper s) ((Z^d)^(B.widths s)) at hP
    change B.profile s ((P.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hp
    rw [hwidth] at hP
    rw [hwidth,hprofile] at hp
    exact hz label s d hd (W s) (B.upper s) (hW s) P hP hp

theorem sourceData_batch_gate {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η→
      B.widths=(fun s=>D.ell s/d)→B.profile=(fun _ y=>(F.w y:ℂ))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin D.N),∀j k : ℕ,∀σ t : ℝ,
      let Bf:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∑u∈Bf.rows,‖polynomial (Bf.family u Bf.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^Bf.m) σ t*
        polynomial (Bf.family u Bf.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^Bf.m) σ t*
          Bf.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters F.modulus ⊤,‖averageWeight (ι:=selected) F.modulus ⊤‖*
          ∑u∈Bf.rows,‖fiberSector le_top Bf η₀ selected j k σ t θ u‖^2 := by
  apply eventually_source_batch_plain_sectors F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad rfl η D.ell (fun s=>(D.slots_bounds s).1) (fun _ y=>(F.w y:ℂ))
  intro s y hy
  have hn : F.w y≠0 := by
    intro h
    apply hy
    simp only [h,Complex.ofReal_zero]
  exact (F.support hn).1.le

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCapacity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeScale HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sectorConductorFactor (η₀ : Character) : ℕ :=
  η₀.modulus.absNorm*fixedConductorFactor*(M.absNorm*η₀.modulus.absNorm)

lemma initial_sector_modulus (η₀ : Character) (u : FreeRow) (θ : RayQuotient.Characters M H) :
    ((naturalRow η₀ u.val u.property.1).character.product (relativeCharacter M H hH η₀ θ)).modulus.absNorm≤
      sectorConductorFactor M η₀*(Ideal.span {u.val}).absNorm := by
  have hn:=(naturalRow η₀ u.val u.property.1).natural_modulus_bound
  have hs:=relativeCharacter_modulus M H hH η₀ θ
  apply (product_modulus_bound _ _).trans
  apply (Nat.mul_le_mul hn hs).trans_eq
  unfold sectorConductorFactor
  ring

theorem eventually_source_sector_capacity
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (margin : ℝ) (hmargin : 0< margin) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),∀d : ℝ,∀u : FreeRow,
      ((Ideal.span {u.val}).absNorm:ℝ)≤Z^(d-margin)→
      ∀θ : RayQuotient.Characters M H,
      (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
        (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)≤Z^margin := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro label d u hu θ
  have hb : (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
      (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)*((Ideal.span {u.val}).absNorm:ℝ) := by
    exact_mod_cast initial_sector_modulus M H hH (sourceMomentBase M H hH S hS η label) u θ
  apply hb.trans
  calc
    _≤Z^margin*Z^(d-margin) := mul_le_mul (hz label) hu (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

theorem sourceData_fiber_sector_capacity {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : HeckeDetectorBatch.Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      (∀u∈B.rows,ProbeHighRowFamily.rowNorm u≤Z^(d-D.t))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀u∈(B.fiber bin label J K hne).rows,∀θ : RayQuotient.Characters F.modulus ⊤,
      (((naturalRow (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
        u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_sector_capacity F.modulus ⊤ le_top
    F.S F.exclusions.prime η D.t D.t_pos] with Z hz
  intro d a ε tstar T allowance i B hcap bin label J K hne u hu θ
  apply hz label d u ?_ θ
  simp only [HeckeDetectorBatch.Batch.fiber, HeckeDetectorFiberPartition.toFiber,
    HeckeDetectorFiberPartition.fiber, Finset.mem_filter] at hu
  have hmem : u∈B.rows := hu.1
  exact hcap u hmem

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSupport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary HeckeDetectorRawFiber ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma oriented_moment_nonzero_base (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O, idealCoeff χ I=if reverse then
      conj (idealCoeff ((momentData η).character (momentElement u)) I)
      else idealCoeff ((momentData η).character (momentElement u)) I)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff η I≠0 := by
  intro he
  have hh:=hc I
  rw [momentData_product_raw,idealCoeff_product,he,zero_mul] at hh
  cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_zero] at hh
  · exact hI hh
  · exact hI hh

lemma fiber_nonzero_initial {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0) : idealCoeff η I≠0 := by
  apply oriented_moment_nonzero_base η (F.family u F.label) u F.reverse ?_ I hI
  simpa only [hdata,momentElement] using F.row_coeff u hu

lemma ideal_nonzero_forcing_coprime (η : Character) (I P : Ideal O)
    (hI : idealCoeff η I≠0) (hP : P∣I) : IsCoprime η.modulus P := by
  have hI0 : I≠0 := by intro h; apply hI; rw [h,map_zero]
  have he : elementCoeff η (idealGenerator I)≠0 := by
    rw [←idealCoeff_span η (idealGenerator_ne_zero I hI0),span_idealGenerator]
    exact hI
  exact CenteredMomentChildRows.old_coefficient_prime_coprime η (idealGenerator I) he P
    (by rwa [span_idealGenerator])

theorem fiber_internal_forcing {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I Q P : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0)
    (hP : P∣I) (hQP : IsCoprime Q P) : IsCoprime (internalQ Q η) P :=
  internalQ_coprime Q P η hQP
    (ideal_nonzero_forcing_coprime η I P (fiber_nonzero_initial F η hdata u hu I hI) hP)

theorem fiber_initial_support_filter {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (s : Finset (Ideal O)) (weight : Ideal O→ℂ) :
    (∑I∈s,idealCoeff (F.family u F.label) I*weight I)=
      ∑I∈s.filter (fun I=>idealCoeff η I≠0),idealCoeff (F.family u F.label) I*weight I := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hIs hnot
  have hzero : idealCoeff (F.family u F.label) I=0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hIs,fiber_nonzero_initial F η hdata u hu I hn⟩)
  rw [hzero,zero_mul]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right

def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

theorem source_retained_sector_nonprincipal (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu

theorem source_energy_split (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=>h.1
  nonexceptional:=fun _ h=>h.2

lemma initialState_width (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):
    (initialState η Q Φ bΦ U δ hU hδ hs hp hη).width=1+δ:=rfl

def detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=>detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem radialMajorant_support_bound:
    ∃bΦ:ℝ,0<bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_label_modulus_eventually (F:ProbeFinalAssembly.SourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma source_keep_iff (F:ProbeFinalAssembly.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma source_fixed_gates (F:ProbeFinalAssembly.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal F) η≠0 ∧
    internalQ (sourceFixedIdeal F) η≤F.modulus ∧
    internalQ (sourceFixedIdeal F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal F) η≤Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72 F)⟩

theorem source_energy_split_state (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (rows:Finset FreeRow)(f:FreeRow→ℂ):
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>initialKeep η (internalQ (sourceFixedIdeal F) η) u.val),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2:=by
  simpa only [source_keep_iff] using source_energy_split F η rows f

theorem source_initial_states (F:ProbeFinalAssembly.SourceData D):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d:ℝ,(1/200:ℝ)≤d→
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label;
      ∃s:NaturalState (Z^d) 0 bΦ,
        s.character=η₀ ∧ s.fixedModulus=internalQ (sourceFixedIdeal F) η₀ ∧
        s.puncture=1 ∧ s.radial.profile=radialMajorant ∧ s.radial.scale=Z^d ∧
        s.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal F) η₀) ∧
        s.rowWidth=1 ∧ s.characterWidth=δ ∧ s.width=1+δ:=by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually F η δ hδ] with Z hz
  intro label d hd
  have hd0:0<d:=by linarith
  have hU:1≤Z^d:=(Real.one_lt_rpow hz.1 hd0).le
  dsimp only
  refine ⟨initialState (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
    (internalQ (sourceFixedIdeal F) (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label))
    radialMajorant bΦ (Z^d) δ hU hδ.le hs
    radialMajorant_nonneg (hz.2 label d hd),?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional

theorem paired_control (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t:ℝ,
      (detectorProfiles reverse j k σ t).control S ^2≤C*(1+‖t‖)^J:=by
  obtain ⟨J,C,hC,h⟩:=detectorSchwartz_uniform S
  refine ⟨4*J,C^4,by positivity,?_⟩
  intro reverse j k hjk σ hσ t
  have hj:=h reverse j (by omega) σ hσ t
  have hk:=h reverse k (by omega) σ hσ t
  have hp:(detectorProfiles reverse j k σ t).control S≤(C*(1+‖t‖)^J)^2:=by
    simpa only [detectorProfiles,Profiles.control,sourceControl,Fin.zero_eta,ite_true,
      show ¬((1:Fin 2)=0) by decide,ite_false,pow_two] using
      mul_le_mul hj hk (sourceControl_nonneg S (detectorSchwartz reverse k σ t)) (by positivity)
  have hs:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
  calc
    _≤((C*(1+‖t‖)^J)^2)^2:=hs
    _=C^4*(1+‖t‖)^(4*J):=by
      rw [←pow_mul,mul_pow,←pow_mul]
      congr 2 ; omega

theorem source_height_factor (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀degree:ℕ,∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height → |t|≤height →
      (detectorProfiles reverse j k σ t).control S ^2*(1+|(0:ℝ)|+height)^degree
        ≤C*(1+height)^(J+degree):=by
  obtain ⟨J,C,hC,h⟩:=paired_control S
  refine ⟨J,C,hC,?_⟩
  intro degree reverse j k hjk σ hσ height t hh ht
  have hb:(detectorProfiles reverse j k σ t).control S ^2≤C*(1+height)^J:=by
    apply (h reverse j k hjk σ hσ t).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Real.norm_eq_abs] using add_le_add le_rfl ht
  simpa only [abs_zero,add_zero,pow_add,mul_assoc] using
    mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith:0≤1+height) degree)

end SevenEighths.CenteredMomentDetectorPlainProfileControl

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceExceptionalBound (F : ProbeFinalAssembly.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤ sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤ rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

theorem eventually_source_sector_gate (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤ rowNorm u→ rowNorm u≤Z^(d-D.t) →
      ∀θ : RayQuotient.Characters F.modulus ⊤,
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      let χ:=(CenteredMomentNaturalRowSource.naturalRow η₀ u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top η₀ θ)
      χ.residue≠1 ∧ (χ.modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_no_exceptional F η,
    eventually_source_sector_capacity F.modulus ⊤ le_top F.S F.exclusions.prime η D.t D.t_pos]
    with Z hn hc
  intro label d u hlo hhi θ
  exact ⟨source_retained_sector_nonprincipal F _ u (hn label u hlo) θ,hc label d u hhi θ⟩

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def retainedSourceEnergy (keep:O→Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem retained_positive_energy_le_source
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      retainedSourceEnergy keep F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=>fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_fibers_eventually_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem source_exceptional_energy_eventually_zero (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀f:FreeRow→ℂ,
      (∑u∈rows.filter (sourceExceptional S
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)),‖f u‖^2)=0:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows label f
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact False.elim ((hz label u (hrows u hu)) hex)

theorem source_batch_plain_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.CenteredMomentDetectorPlainExceptional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainStateDictionary
open HeckeFamily HeckeDetectorRawFiber HeckePrimeAnnular
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

lemma plainProfile_eq_detectorSchwartz
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(j:ℕ)(σ t:ℝ):
    plainProfile F j σ t=(detectorSchwartz F.reverse j σ t:ℝ→ℂ):=by
  funext x
  exact (detectorSchwartz_apply F.reverse j σ t x).symm

theorem retainedSourceEnergy_eq_energy
    (keep:O→Prop)(F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ))(hU:0<U):
    retainedSourceEnergy keep F η selected j k σ t Φ=
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (plainProfile F j σ t) (plainProfile F k σ t)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m) keep Φ U:=by
  exact (positive_energy_eq_complete_source η 0 keep
    (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (fun _=>Real.rpow_pos_of_pos hU _)
    (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) Φ U).symm

theorem retainedSourceEnergy_empty_eq_plainEnergy
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (initialState η Q Φ bΦ U δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=by
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  simp [initialState,NaturalState.mask,detectorProfiles,positiveSlotRow]

end SevenEighths.CenteredMomentDetectorPlainStateDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeGate -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRowMask CenteredMomentFixedRayInducingTransport
local notation "O" => HeckeFamily.O

def relativeBase (η : Character) (u : FreeRow) : Character :=
  (naturalRow η u.val u.property.1).character.product η.inverse

variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_relativeBase_twists (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : ¬sourceExceptional F η u) :
    ∀θ : RayQuotient.Characters F.modulus ⊤,
      (twistedFamily F.modulus ⊤ le_top (relativeBase η u) θ).residue≠1 := by
  have hn : ¬FixedInducingRow η (internalQ (sourceFixedIdeal F) η) fixedBadMask 1 u.val := by
    intro h
    apply hu
    exact (fixedInducingRow_mul_mask_iff η _ fixedBadMask (idealGenerator 1) 1 u.val
      fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero) one_ne_zero u.property.1
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h
  have hn' : ¬FixedInducingRow (η.product η.inverse) (internalQ (sourceFixedIdeal F) η)
      fixedBadMask 1 u.val :=
    (not_fixedInducingRow_product_iff η η.inverse _ fixedBadMask 1 u.val inf_le_right
      fixedBadMask_ne_zero one_ne_zero u.property.1 (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hn
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal F.modulus ⊤ le_top
    (η.product η.inverse) (relativeBase η u) (internalQ (sourceFixedIdeal F) η)
    fixedBadMask 1 u.val ?_ (inf_le_left.trans (sourceFixedIdeal_le_modulus F)) hn'
  exact product_row_presentation η (naturalRow η u.val u.property.1).character η.inverse
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η u.val u.property.1).element)

lemma relativeBase_modulus (M : Ideal O) [NeZero M] (η : Character) (u : FreeRow) :
    (relativeBase η u).modulus.absNorm≤ sectorConductorFactor M η*(Ideal.span {u.val}).absNorm := by
  have hb:=(HeckePrimeScale.product_modulus_bound (naturalRow η u.val u.property.1).character η.inverse).trans
    (Nat.mul_le_mul_right η.modulus.absNorm (naturalRow η u.val u.property.1).natural_modulus_bound)
  have hM : 1≤M.absNorm := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  have hm : η.modulus.absNorm≤M.absNorm*η.modulus.absNorm := by nlinarith
  change (relativeBase η u).modulus.absNorm≤_
  apply hb.trans
  unfold sectorConductorFactor
  calc
    _=(η.modulus.absNorm*fixedConductorFactor*η.modulus.absNorm)*(Ideal.span {u.val}).absNorm := by ring
    _≤_ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)

theorem eventually_source_relativeBase_gate (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤ rowNorm u → rowNorm u≤Z^(d-D.t) →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^d ∧
        ∀θ : RayQuotient.Characters F.modulus ⊤,
          (twistedFamily F.modulus ⊤ le_top (relativeBase η₀ u) θ).residue≠1 := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)≤Z^D.t := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop D.t_pos).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_source_no_exceptional F η,eventually_gt_atTop (0:ℝ)] with Z hc hn hZ
  intro label d u hlo hhi
  refine ⟨?_,source_relativeBase_twists F _ u (hn label u hlo)⟩
  have hb : ((relativeBase (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u).modulus.absNorm:ℝ)≤
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)*rowNorm u := by
    change _≤_*((Ideal.span {u.val}).absNorm:ℝ)
    exact_mod_cast relativeBase_modulus F.modulus _ u
  apply hb.trans
  calc
    _≤Z^D.t*Z^(d-D.t) := mul_le_mul (hc label) hhi (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot HeckeZeroSupremum
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_physical_slot_bound (F : ProbeFinalAssembly.SourceData D)
    (loss lo hi κ : ℝ) (hloss : 0<loss) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d : ℝ,d≤1 →
      ∀u : FreeRow,Z^(1/100:ℝ)≤ rowNorm u → rowNorm u≤Z^(d-D.t) →
      ∀P t : ℝ,1≤P → P≤Z → ∀z : ℂ,lo≤1-z.re → 1-z.re≤hi →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ‖normalizedSlot η₀ fixedBadMask 1 u.val (primePool F.modulus ⊤ 2 P)
        (physicalSlotCoefficient η₀ F.W P z) t P‖^2≤
        C*(1+|t|+|z.im|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    F.modulus ⊤ le_top F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    1 1 loss lo hi κ (by norm_num) (by norm_num) hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η
  filter_upwards [eventually_source_relativeBase_gate F η,eventually_ge_atTop Z₀,
    eventually_ge_atTop (1:ℝ)] with Z hgate hZ0 hZ
  intro label d hd u hlo hhi P t hP hPZ z hzlo hzhi
  let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  obtain ⟨hc,hn⟩:=hgate label d u hlo hhi
  have hc' : ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^(1:ℝ) :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le hZ hd)
  have hb:=hbound Z P hZ0 hP (by simpa only [Real.rpow_one] using hPZ)
    (relativeBase η₀ u) hc' hn (1-z.re) (t-z.im) hzlo hzhi
  have hconj : (fun y=>conj (F.W y))=(F.W:ℝ→ℂ) := by
    funext y
    rw [F.complex_eq]
    simp
  dsimp only
  rw [physicalSlot_eq_relativeRay F.modulus ⊤ η₀ (naturalRow η₀ u.val u.property.1).character
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η₀ u.val u.property.1).element)
    F.W 2 P t z (zero_lt_one.trans_le hP),hconj,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  have habs : |t-z.im|≤|t|+|z.im| := by simpa using (abs_sub_le t 0 z.im)
  exact pow_le_pow_left₀ (by positivity) (by linarith) degree

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckeZeroSupremum
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRayInducingTransport CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

lemma natural_relative_twists {η : Character} {z : O} (F : NaturalRow η z) (hz : z≠0)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) :
    ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue≠1 := by
  have hn : ¬FixedInducingRow (η.product η₀.inverse) (internalQ Q η₀) fixedBadMask 1 z :=
    (not_fixedInducingRow_product_iff η η₀.inverse _ fixedBadMask 1 z inf_le_right
      fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hex
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal M H hH
    (η.product η₀.inverse) (F.character.product η₀.inverse) (internalQ Q η₀)
    fixedBadMask 1 z ?_ (inf_le_left.trans hQM) hn
  exact product_row_presentation η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)

include hH

theorem natural_relative_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff η₀.inverse I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (η₀.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hη₀ hZ
  intro P hP hPcap η z hz F hcond Q hQM hex σ t v hσ hσhi
  have hc : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤Z^(Lmod+1) := by
    have hb : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤
        (F.character.modulus.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound F.character η₀.inverse
    apply hb.trans
    calc
      _≤Z^Lmod*Z := mul_le_mul hcond hη₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1) := by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound Z P hZ0 hP hPcap (F.character.product η₀.inverse) hc
    (natural_relative_twists M H hH F hz η₀ Q hQM hex) σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_eq_ray M H η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W b P σ t v (zero_lt_one.trans_le hP),norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

theorem natural_character_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ν : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν.inverse] with Z hz
  intro P hP hPcap η z hz0 F hcond Q hQM hQν hex σ t v hσ hσhi
  have hQeq : internalQ Q ν.inverse=Q := inf_eq_left.mpr hQν
  have he:=hz P hP hPcap η z hz0 F hcond Q hQM (by simpa only [hQeq] using hex) σ t v hσ hσhi
  simpa only [idealCoeff_inverse_conj,starRingEnd_self_apply] using he

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceRayPrime -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_slot_product {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  let el : ℝ := loss/(F.card+1)
  have hel : 0<el := div_pos hloss (by positivity)
  obtain ⟨J,C,hC,hbound⟩ := natural_ray_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot el lo hi κ hLm hLs hel hbeta hκ
  let C₀ := max 1 C
  have hC₀ : 1≤C₀ := le_max_left _ _
  refine ⟨J*F.card,C₀^F.card,pow_pos (zero_lt_one.trans_le hC₀) _,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η z hz0 N hmod Q hQM hex A hAF
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0≤κ := by linarith
  have hh : 1≤1+|t|+T := by linarith [abs_nonneg t]
  have hslot (i : α) (hi : i∈A) :
      ‖naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      (C₀*(1+|t|+T)^J)*Z^(el+κ*w i) := by
    rw [natural_slot_eq N]
    have he := hz (θ i) (Z^(w i)) (Real.one_le_rpow hZ.le (hw i (hAF hi)))
      (Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i (hAF hi))) η z hz0 N hmod Q hQM hex
      (σ i) t (v i) (hσlo i (hAF hi)) (hσhi i (hAF hi))
    apply he.trans
    rw [←Real.rpow_mul hZ0.le]
    calc
      _ ≤ (C₀*(1+|t|+T)^J)*Z^el*Z^(w i*κ) := by
        gcongr
        · exact le_max_right 1 C
        · exact hv i (hAF hi)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hZ0]; congr 2 ; ring
  rw [norm_prod,←Finset.prod_pow]
  apply (Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZ0]
  have hexp : (∑i∈A,(el+κ*w i))≤loss+κ*(∑i∈F,w i) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have hc : (A.card:ℝ)≤F.card+1 := by exact_mod_cast (Finset.card_le_card hAF).trans (Nat.le_succ _)
    have he : (A.card:ℝ)*el≤loss := by
      calc
        _ ≤ (F.card+1)*el := mul_le_mul_of_nonneg_right hc hel.le
        _ = _ := by dsimp [el]; field_simp
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hAF (fun i hi _=>hw i hi)
    nlinarith
  have hp : 1≤C₀*(1+|t|+T)^J := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hh)
  apply (mul_le_mul (pow_le_pow_right₀ hp (Finset.card_le_card hAF))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)).trans_eq
  rw [mul_pow,←pow_mul]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.AllocatedChildren -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma natural_product_eq_positive {η:Character}{z:O}(F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i)=
      CenteredMomentRetainedEnergy.positiveSlotRow η
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 z
        W₁ W₂ pool β P 0 X₁ X₂:=by
  rw [natural_unit_mask_positive F]
  have hh:=positiveSlotRow_eq_product η F.character fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W₁ W₂ pool β P X₁ X₂ 0 0 hX₁ hX₂ hP
  rw [twistProfile_zero,twistProfile_zero] at hh
  rw [hh]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hs:=CenteredMomentRayMaskedFloor.natural_slot_eq F (pool i) (β i) (P i) 0
  have he:heightCoefficient (β i) 0=β i:=by
    funext I
    simp only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  rw [he] at hs
  exact hs

lemma natural_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂ pool β P
      X₁ X₂ r.keep r.profile r.scale:=by
  unfold radialEnergy CenteredMomentInductionEnergy.energy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk,naturalCharacter_eq η z (hz z hk)]
    rw [natural_product_eq_positive (naturalRow η z (hz z hk)) W₁ W₂ pool β P X₁ X₂ hX₁ hX₂ hP]
  · simp only [ite_eq_right hk]

omit [Fintype α] in
lemma natural_subset_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (F:Finset α)(W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ r.keep r.profile r.scale:=by
  have hh:=natural_radial_eq_energy (α:=F) η r hz W₁ W₂
    (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ hX₁ hX₂
    (fun i=>hP i i.property)
  have hp (z:O):(∏i:F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))=
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i):=
    Finset.prod_coe_sort F (fun i:α=>naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
  simp_rw [hp] at hh
  exact hh

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum

def allocatedEnergy (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α):ℝ:=
  CenteredMomentInductionEnergy.energy (ι := ↥(liveIndices D a\J)) η
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)) 1 0
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    (fun i:↥(liveIndices D a\J)=>pool i) (fun i:↥(liveIndices D a\J)=>heightCoefficient (β i) t)
    (fun i:↥(liveIndices D a\J)=>P i)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    r.keep r.profile r.scale

lemma child_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α)
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>child (α:=α) (naturalCharacter η z) D a V₁ V₂ pool β P
      t X₁ X₂ hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale=
      allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J:=by
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  exact natural_subset_radial_eq_energy η r hz (liveIndices D a\J)
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    pool (fun i=>heightCoefficient (β i) t) P
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂) (fun i _=>hP i)

def commonAllocatedEnergy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)):ℝ:=
  let d:=commonData (withHeight s τ v) C R B
  if left then allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma commonChild_energy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(hz:∀z,r.keep z→z≠0)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>commonChild s τ v C R B D a V₁ V₂ left z D₁ D₂ J)
      r.keep r.profile r.scale=commonAllocatedEnergy s τ v C R B D a V₁ V₂ r left D₁ D₂ J:=by
  let d:=commonData (withHeight s τ v) C R B
  cases left
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J hD₁ hD₂
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J hD₁ hD₂

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.AllocatedBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentNaturalRowSource CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem actual_common_from_energy (b M:α→ℝ)(hM:∀i,0≤M i)(ε:ℝ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀s:Input α,(∀i,s.hi i≤b i)→(∀i,s.M i≤M i)→
    ∀(τ:Character)(v:ℝ)(C R:Ideal O),R≠0→∀B:actualAllocations s.pools C,
    ∀(L:Ideal O)(a:Allocation L (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂:Plain,V₁.W=s.W₁→V₂.W=s.W₂→∀r:Radial,(∀z,r.keep z→z≠0)→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀left:Bool,∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
      ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      commonAllocatedEnergy s τ v C R B L a V₁ V₂ r left D₁ D₂ J≤(if left then E₁ else E₂))→
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂):=by
  obtain ⟨C₀,hC₀,hbound⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂ he
  apply hbound s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz true D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he true D₁ hD₁ D₂ hD₂ J hJ
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz false D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he false D₁ hD₁ D₂ hD₂ J hJ

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

 theorem slot_coefficient_bounds (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B : ℝ,0<B ∧ ∀(ν : Character)(P σ v t : ℝ),0<P → lo≤σ → σ≤hi →
    ∀I : Ideal O,I≠0 →
      ‖heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I‖≤B ∧
      (heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I≠0 →
        (I.absNorm:ℝ)≤b*P) := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  constructor
  · apply (show ‖idealCoeff ν I*annularWeight W P σ v I‖≤‖annularWeight W P σ v I‖ by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ν I)).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs
  · intro hn
    have hw : W ((I.absNorm:ℝ)/P)≠0 := by
      intro hh
      exact hn (by simp [heightCoefficient,annularWeight,hh])
    exact (div_le_iff₀ hP).mp (hWs hw).2

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowError -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceHomogeneousError QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem relative_slot_error {α:Type*}(F:Finset α)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi bshort:ℝ)(ha:0<aslot)
    (hs:Function.support Wslot⊆Set.Icc aslot bslot)(hc:Continuous Wslot):
    ∃C:ℝ,0<C ∧ ∀T:Finset α,T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→Character)(ν:α→Character)(pool:α→Finset (Ideal O))
        (P σ freq:α→ℝ)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) → (∀i∈T,lo≤σ i) → (∀i∈T,σ i≤hi) →
      (∀i∈T,∀I∈pool i,Prime I) → (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i)
          (heightCoefficient (fun I=>idealCoeff (ν i) I*
            HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  obtain ⟨B,hB,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi ha hs hc
  obtain ⟨C,hC,he⟩:=natural_reference_error_homogeneous F bshort
    (fun _=>bslot) (fun _=>B) (fun _ _=>hB.le)
  refine ⟨C,hC,?_⟩
  intro T hT W hW χ ν pool P σ freq t X K Φ keep hX hK hP hlo hhi hp hΦ
  apply he T hT W hW χ pool
    (fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
    P t X K Φ keep hX hK hP hp
  · intro i hi I hI
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hb
  · intro i hi I hI hn
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).2
    apply hb
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hΦ

end SevenEighths.CenteredMomentEnergyReferenceLowError

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorNatural -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ),Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → ∀A : Finset α,A⊆F →
      radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,Cs,hCs,hslot⟩ := natural_slot_product M H hH F W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨S,Cp,hCp,hplain⟩ := global_positive_scale a₀ b₀ ha₀
  refine ⟨J,S,Cp^4*3^8*Cs,by positivity,?_⟩
  intro η₀
  filter_upwards [hslot η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ A hAF
  let E := Cs*(1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hE : 0≤E := by dsimp [E]; positivity
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0≤B₁ := apply_nonneg _ _
  have hB₂ : 0≤B₂ := apply_nonneg _ _
  let B := Cp^2*(B₁*B₂)*Qbound^2*3^4*Real.sqrt E
  have hB : 0≤B := by dsimp [B]; positivity
  have hpoint (z : O) (hkeep : r.keep z) :
      ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖≤B := by
    have hn := hz z hkeep
    have heq := naturalCharacter_eq η z hn
    have hnon : (naturalCharacter η z).residue≠1 := by
      rw [heq]
      exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η
        (naturalRow η z hn).character (internalQ Q η₀) fixedBadMask 1 z
        (by simpa only [one_mul] using (naturalRow η z hn).element) (hex z hkeep)
    have h₁ : ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0‖≤Cp*B₁*Qbound*3^2 := by
      have he := hplain W₁ hs₁ _ hnon X₁ 0 hX₁
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₁)) (show (0:ℝ)≤9 by norm_num))
    have h₂ : ‖polynomial (naturalCharacter η z) false W₂ X₂ 0 0‖≤Cp*B₂*Qbound*3^2 := by
      have he := hplain W₂ hs₂ _ hnon X₂ 0 hX₂
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₂)) (show (0:ℝ)≤9 by norm_num))
    have hs := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η z hn (naturalRow η z hn)
      (by simpa only [heq] using hmod z hkeep) Q hQM (hex z hkeep) A hAF
    rw [←heq] at hs
    have hsroot := (Real.le_sqrt (norm_nonneg _) hE).mpr hs
    rw [norm_mul,norm_mul]
    apply (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
      hsroot (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B,B₁,B₂]
    norm_num only [abs_zero,add_zero]
    ring
  have he := radial_bound_on_keep _ r B hB hpoint
  apply he.trans_eq
  dsimp [B,E,B₁,B₂]
  rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hE]
  ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorShared -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem masked_natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0*
        polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0*
        ∏i∈F,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := natural_pair_slots M H hH F W a b ha hWs hW a₀ b₀ ha₀
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W a b lo hi ha hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F (fun _=>b) (fun _=>B) (fun _ _=>hB.le) ε hε
  refine ⟨J,S,Cd*C,mul_pos hCd hC,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hd := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hp (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) : Prime I :=
    (Finset.mem_filter.mp hI).2.1
  have hc (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) :=
    hcoeff (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (v i) t
      (Real.rpow_pos_of_pos hZ0 _) (hσlo i hi) (hσhi i hi) I (hp i hi I hI).ne_zero
  have he := hdelete (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    W₁ W₂ X₁ X₂ a₀ b₀ a₀ b₀ (fun i=>primePool M H b (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    (fun i=>Z^(w i)) r.keep r.profile r.scale E hX₁ hX₂ hb₀ hb₀ hs₁ hs₂ hp
    (fun _ _=>Real.rpow_pos_of_pos hZ0 _) (fun i hi I hI=>(hc i hi I hI).1)
    (fun i hi I hI=>(hc i hi I hI).2) r.scale_pos r.nonneg hE ?_
  · rw [primeSupport_product_radical R hR] at he
    exact he.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ A hA
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    exact hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
      W₁ W₂ hs₁ hs₂ _ _ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂))
      (F\A) Finset.sdiff_subset

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem original_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := masked_natural_pair_slots M H hH (Finset.univ : Finset α)
    W a b ha hWs hW a₀ b₀ ε ha₀ hb₀ hε Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨n,T₀,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a₀ b₀ ha₀ S
  refine ⟨4*n+J,T₀,C*Ct^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hexbase (z : O) (hk : r.keep z) :
      ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z := by
    intro hh
    apply hex z hk
    exact (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η (internalQ Q η₀)
      fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero (hz z hk)
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh
  let V₁ := CenteredMomentLattice.normPowerProfile W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t
  let V₂ := CenteredMomentLattice.normPowerProfile W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hZ θ w σ v t T (fun i _=>hw i) (fun i _=>hwL i)
    (fun i _=>hσlo i) (fun i _=>hσhi i) hT (fun i _=>hv i)
    η Q r Qbound R hR hQM hQbound hz hexbase hmod hQ V₁ V₂ hv₁ hv₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale =
    radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false V₁ X₁ 0 0*
      polynomial (excluded (naturalCharacter η z) R) false V₂ X₂ 0 0*
      ∏i,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
      r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · simp only [hk,ite_true]
      rw [original_positive_normalized (naturalRow η z (hz z hk)) R hR W₁ W₂
        a₀ b₀ a₀ b₀ ha₀ ha₀ hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
        _ _ _ (fun i=>Real.rpow_pos_of_pos hZ0 _) t X₁ X₂ hX₁ hX₂]
      rw [norm_mul,norm_mul,positive_height_phase_norm X₁ t hX₁,
        positive_height_phase_norm X₂ t hX₂,one_mul,one_mul,naturalCharacter_eq η z (hz z hk)]
    · simp only [hk,ite_false]
  rw [hid]
  apply he.trans
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ *
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    have hheight : (1+‖t‖)^(4*n)≤(1+|t|+T)^(4*n) := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Real.norm_eq_abs]
      linarith
    calc
      _ ≤ (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(1+‖t‖)^n*
        (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)*(1+‖t‖)^n))^2 := hh
      _ = (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
          rw [Nat.mul_comm 4 n,pow_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hheight (by positivity)
  have hd := diagonalControl_nonneg r.profile
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
      ((Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n))*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i,w i)) := by gcongr
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (L Lslot loss lo hi κ bΦ : ℝ) (hL : 0≤L) (hbΦ : 0≤bΦ) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(R : Ideal O),R≠0 → Q≤M →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
    ∀(m q ρ : ℝ),0≤ m → 0≤q → m+q≤ρ → ρ≤L → r.scale=Z^m →
      (η.modulus.absNorm:ℝ)≤Z^q →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
         (1+|t|+T)^degree*Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := original_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ ε ha₀ hb₀ hε (L+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  let Fc : ℝ := fixedConductorFactor
  have hFc : 0<Fc := by
    unfold Fc fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨J,S,C*Fc^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_ge_atTop (Fc*bΦ),eventually_ge_atTop (1:ℝ)] with Z hZ hconst hZ1
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r R hR hQM hz hex hsΦ
    m q ρ hm hq hρ hρL hscale hη W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  have hmod (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Fc*bΦ*Z^ρ := by
    have hn := hz z hk.1
    rw [naturalCharacter_eq η z hn]
    have hrow : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ hk.2)
    have he := (naturalRow η z hn).modulus_power_bound Z q m bΦ hZ0 hbΦ hη hrow
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hFc.le hbΦ)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hcap (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^(L+1) := by
    apply (hmod z hk).trans
    calc
      _ ≤ Z*Z^L := mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_le hZ1 hρL)
        (Real.rpow_nonneg hZ0.le _) hZ0.le
      _ = _ := by rw [Real.rpow_add hZ0,Real.rpow_one]; ring
  have he := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r'
    (Fc*bΦ*Z^ρ) R hR hQM (by positivity) (fun z hk=>hz z hk.1)
    (fun z hk=>hex z hk.1) hcap hmod W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r'.keep r'.profile r'.scale =
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [hid] at he
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ1 hm)] at he
  rw [hscale]
  apply he.trans_eq
  have hzpow : Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))=Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    norm_num
    ring
  calc
    _ = (C*Fc^4*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
      (1+|t|+T)^J)*(Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))) := by ring
    _ = _ := by rw [hzpow]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorState -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hbΦ : 0<bΦ) (hmask : 0≤Bmask)
    (hε : 0<ε) (hLs : 0≤Lslot) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤T → (∀i,|v i|≤T) →
    ∀(Q : Ideal O),Q≤M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤ s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0<e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  obtain ⟨J,S,C,hC,hfloor⟩ := natural_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ e ha₀ hb₀ he (ε/16) Lslot (ε/4) lo hi κ bΦ (by positivity) hbΦ.le hLs
    (by positivity) hbeta hκ
  refine ⟨J,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro η₀
  filter_upwards [hfloor η₀] with Z hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hZ1 := s.base_ge_one
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  have hrad : (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hex (z : O) (hz : s.radial.keep z) :
      ¬CenteredExceptionalProfile.FixedInducingRow s.character (internalQ Q η₀)
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z := by
    rw [←hQ]
    exact s.nonexceptional z hz
  have hh := hZ θ w σ v t T hw hwL hσlo hσhi hT hv s.character Q s.radial s.puncture
    s.puncture_ne_zero hQM s.row_ne_zero hex s.radial_support s.rowWidth s.characterWidth
    (ε/16) s.row_nonneg s.character_nonneg hs le_rfl s.scale_eq s.modulus_bound
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂
  have hwidth : s.rowWidth≤ s.width := by dsimp [NaturalState.width]; linarith [s.character_nonneg]
  have hbudget : Bmask*e+(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤ s.width+ε := by
    linarith
  have hpow : Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤Z^(s.width+ε) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  have hd := diagonalControl_nonneg s.radial.profile
  have hc := p.control_nonneg S
  apply hh.trans
  change C*(s.puncture.radical.absNorm:ℝ)^e*diagonalControl s.radial.profile*bΦ^4*
    (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤_
  calc
    _ ≤ C*Z^(Bmask*e)*diagonalControl s.radial.profile*bΦ^4*
      (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i)) := by gcongr
    _ = (C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^J)*
      (Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.Bands -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def length (Z X:ℝ):ℝ:=Real.logb Z (max 1 X)

lemma length_nonneg (Z X:ℝ)(hZ:1<Z):0≤length Z X:=
  Real.logb_nonneg hZ (le_max_left _ _)

def ZeroAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

lemma zeroAt_of_zeroBound (Q:Ideal O)(a b bΦ Bmask L M ε Z Z₀:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:ZeroBound Q a b bΦ Bmask M ε degree S C Z₀)(hZ:Z₀≤Z):
    ZeroAt Q a b bΦ Bmask L M ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ _ _
  exact h Z hZ s hQ hs p t X₁ X₂ hX₁ hX₂

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem exists_positive_bottom (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L Lslot lo hi ε κ:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε)(hLs:0≤Lslot)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
          (ε/16) ε κ Z η₀ Q degree S C:=by
  have hs (T:Finset α):=CenteredMomentRayMaskedFloor.exists_positive_floor (α:=T)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask ε Lslot lo hi κ
    ha hb hbΦ hmask hε hLs hbeta hκ
  choose J S C hC hbound using hs
  let S₀:Finset (ℕ×ℕ):=Finset.univ.biUnion S
  let C₀:ℝ:=1+∑T:Finset α,C T
  have hC₀:0<C₀:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
    dsimp [C₀];linarith
  refine ⟨∑T:Finset α,J T,S₀,C₀,hC₀,?_⟩
  intro η₀
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr (fun T=>hbound T η₀)
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hslots:6*κ*(∑i,w i)≤ s.width:=by
    linarith [length_nonneg Z X₁ hZ1,length_nonneg Z X₂ hZ1]
  have hh:=hZ T θ w σ v t height hw hwL hσlo hσhi hheight hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hsub:S T⊆S₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hpc:p.control (S T)≤p.control S₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hc:C T≤C₀:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
      (Finset.mem_univ T)
    dsimp [C₀];linarith
  have hj:J T≤∑T:Finset α,J T:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hpow:(1+|t|+height)^(J T)≤(1+|t|+height)^(∑T:Finset α,J T):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=p.control_nonneg S₀
  have hpt:=p.control_nonneg (S T)
  apply hh.trans
  gcongr
end SevenEighths.CenteredMomentEnergyBands

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.AllocatedZero -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedZero
open HeckeFamily CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma allocatedScale_le (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(X:ℝ)(hX:0<X)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):
    clippedScale (rawScale D a X j)/(Ideal.absNorm (∏I∈F,I):ℝ)≤ max 1 X:=by
  have hn:1≤(Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a j):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hf:1≤(Ideal.absNorm (∏I∈F,I):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr hF))
  have hx:rawScale D a X j≤X:=div_le_self hX.le hn
  exact (div_le_self (by unfold clippedScale;positivity) hf).trans
    (max_le_max_left 1 hx)

lemma allocated_empty (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O)):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)=
      CenteredMomentCoreFloor.zeroEnergy η
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
        (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
        (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
        (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
        (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) r:=by
  let : IsEmpty ↥(liveIndices D a\liveIndices D a):=⟨fun i=>by
    have hi:=Finset.mem_sdiff.mp i.property
    exact hi.2 hi.1⟩
  simp only [allocatedEnergy,energy,CenteredMomentCoreFloor.zeroEnergy,
    CenteredMomentCoreFloor.zeroRow,positiveSlotRow,Fintype.prod_empty,mul_one]

theorem empty_from_zeroAt (lo hi Z Bmask bΦ L Mcap ε:ℝ)(hlo:0<lo)(hL:0≤L)
    (Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hz:ZeroAt Q (lo/max 1 hi) hi bΦ Bmask L Mcap ε Z degree S C)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hwidth:s.width≤Mcap)
    (hunit:s.puncture=1)(p:Profiles lo hi)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0)
    (hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L):
    let V₁:=sourcePlain lo hi hlo (p.profile 0) (p.support 0)
    let V₂:=sourcePlain lo hi hlo (p.profile 1) (p.support 1)
    let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
    let hU:∀i,0<U i:=by intro i;fin_cases i;exact rawScale_pos D a X₁ hX₁ 0;exact rawScale_pos D a X₂ hX₂ 1
    allocatedEnergy s.character s.radial D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)≤
      C*diagonalControl s.radial.profile*((retainedPair lo hi hlo p U hU t).control S)^2*
        Z^(s.width+ε):=by
  dsimp only
  rw [allocated_empty]
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
  have hU:∀i,0<U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D a X₁ hX₁ 0
    · exact rawScale_pos D a X₂ hX₂ 1
  have hh:=hz s hQ hwidth (retainedPair lo hi hlo p U hU t) 0
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂)
    ((allocatedScale_le D a X₁ hX₁ 0 D₁ hD₁).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₁))
    ((allocatedScale_le D a X₂ hX₂ 1 D₂ hD₂).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₂))
  rw [NaturalState.plainEnergy_eq_zero] at hh
  simpa only [NaturalState.mask,hunit,retainedPair,U,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,norm_zero,zero_add,abs_zero,add_zero,one_pow,mul_one] using hh

end SevenEighths.CenteredMomentEnergyAllocatedZero

end

end OAI

end

