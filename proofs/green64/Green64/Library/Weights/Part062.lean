module

public import Green64.Library.Weights.NumericSeenKernelLift
public import Green64.Library.Analysis.Estimates.B26SmallOldFourierEnergy
public import Green64.Library.Weights.Part060
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part058
public import Green64.Library.Weights.B26TiltedAveragedAuxBan
public import Green64.Library.Weights.Part055

@[expose] public section

/-!
# Weights / Part062

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalNumericSeenFamilyLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- A coherent family of literal fresh-history rows. Each pattern has
its OWN fresh target set; a single arbitrary future reads the respective
updated numerical seen. All signed coefficients remain inside row. -/
def sourceOriginalNumericSeenFamilyLift434
    {X I : Type} [Fintype X] [DecidableEq I]
    (family : Finset I) (birth : I → X → Finset ℕ)
    (gate : X → Finset ℕ → Prop)
    (row : Finset ℕ → I → X → X → ℂ)
    (f : X → Finset ℕ → ℂ) (x : X) (S : Finset ℕ) : ℂ :=
  if gate x S then
    ∑ i ∈ family, ∑ y : X, row S i x y *
      (if Disjoint S (birth i y) then f y (S ∪ birth i y) else 0)
  else 0

/-- A coherent all-pattern bilinear estimate survives the actual
pattern-dependent numerical history update. The ONLY new loss is the
number of patterns, never the number of histories. The unmarked
arithmetic estimate must allow independently chosen coupled endpoint
tests for each pattern. It is supplied by the actual B26 theorem below. -/
theorem source_original_NUMERIC_SEEN_family_bilinear_lift434
    {X I : Type} [Fintype X] [DecidableEq I]
    (pool : Finset ℕ) (family : Finset I)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (birth : I → X → Finset ℕ)
    (hbirth : ∀ i ∈ family, ∀ y, birth i y ⊆ pool)
    (gate : X → Finset ℕ → Prop)
    (row : Finset ℕ → I → X → X → ℂ)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPair : ∀ S ∈ pool.powerset, ∀ (U : X → ℂ) (V : I → X → ℂ)
      (ET : ℝ), 0 ≤ ET →
      (∀ i ∈ family, (∑ y : X, w y*‖V i y‖^2) ≤ ET) →
      ‖∑ i ∈ family, ∑ x : X,
        (w x:ℂ)*star (U x)*(∑ y : X, row S i x y*V i y)‖^2 ≤
        delta*(∑ x : X, w x*‖U x‖^2)*ET)
    (f : X → Finset ℕ → ℂ) :
    sourceOriginalNumericSeenEnergy434 pool w
      (sourceOriginalNumericSeenFamilyLift434 family birth gate row f) ≤
      (delta*(family.card:ℝ))*sourceOriginalNumericSeenEnergy434 pool w f := by
  let v := fun S : Finset ℕ => fun i : I => fun y : X =>
    if Disjoint S (birth i y) then f y (S ∪ birth i y) else 0
  let ET := fun S : Finset ℕ => ∑ i ∈ family, ∑ y : X, w y*‖v S i y‖^2
  have hv (S : Finset ℕ) (i : I) : 0 ≤ ∑ y : X, w y*‖v S i y‖^2 :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hw y) (sq_nonneg _))
  have hlocal (S : Finset ℕ) (hS : S ∈ pool.powerset) :
      (∑ x : X, w x*
        ‖sourceOriginalNumericSeenFamilyLift434 family birth gate row f x S‖^2) ≤
      delta*ET S := by
    let out := fun x : X => sourceOriginalNumericSeenFamilyLift434 family birth gate row f x S
    let E := ∑ x : X, w x*‖out x‖^2
    have hE : 0 ≤ E := Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    have hET : 0 ≤ ET S := Finset.sum_nonneg (fun i _ => hv S i)
    have hcap (i : I) (hi : i ∈ family) : (∑ y : X, w y*‖v S i y‖^2) ≤ ET S :=
      Finset.single_le_sum (fun j _ => hv S j) hi
    have hn (z : ℂ) : ((‖z‖^2:ℝ):ℂ)=star z*z := by
      simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using
        (Complex.normSq_eq_conj_mul_self (z := z))
    have he :
        (∑ i ∈ family, ∑ x : X,
          (w x:ℂ)*star (out x)*(∑ y : X, row S i x y*v S i y))=(E:ℂ) := by
      rw [Finset.sum_comm]
      dsimp only [E]
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [←Finset.mul_sum]
      by_cases hg : gate x S
      · have ho : out x=∑ i ∈ family,∑ y : X,row S i x y*v S i y := by
          simp only [out,sourceOriginalNumericSeenFamilyLift434,if_pos hg,v]
        rw [←ho,Complex.ofReal_mul,hn]
        ring
      · have ho : out x=0 := by simp only [out,sourceOriginalNumericSeenFamilyLift434,if_neg hg]
        simp [ho]
    have hh := hPair S hS out (v S) (ET S) hET hcap
    rw [he] at hh
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE] at hh
    change E ≤ delta*ET S
    by_cases hz : E=0
    · rw [hz]
      exact mul_nonneg hdelta hET
    · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
      change E^2 ≤ delta*E*ET S at hh
      nlinarith
  have hsingle (i : I) (hi : i ∈ family) :
      (∑ S ∈ pool.powerset, ∑ y : X, w y*‖v S i y‖^2) ≤
      sourceOriginalNumericSeenEnergy434 pool w f := by
    unfold sourceOriginalNumericSeenEnergy434
    rw [Finset.sum_comm,Finset.sum_comm (s := pool.powerset)]
    apply Finset.sum_le_sum
    intro y hy
    rw [←Finset.mul_sum,←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw y)
    have he (S : Finset ℕ) :
        ‖v S i y‖^2 =
        if Disjoint S (birth i y) then ‖f y (S ∪ birth i y)‖^2 else 0 := by
      dsimp only [v]
      split_ifs <;> simp
    simp_rw [he]
    exact source_original_NUMERIC_SEEN_update_energy434 pool (birth i y) (hbirth i hi y) (f y)
  have htotal : (∑ S ∈ pool.powerset,ET S) ≤
      (family.card:ℝ)*sourceOriginalNumericSeenEnergy434 pool w f := by
    dsimp only [ET]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i ∈ family,sourceOriginalNumericSeenEnergy434 pool w f :=
        Finset.sum_le_sum (fun i hi => hsingle i hi)
      _ = _ := by simp
  calc
    _ ≤ ∑ S ∈ pool.powerset,delta*ET S :=
      Finset.sum_le_sum (fun S hS => hlocal S hS)
    _ = delta*(∑ S ∈ pool.powerset,ET S) := by rw [Finset.mul_sum]
    _ ≤ delta*((family.card:ℝ)*sourceOriginalNumericSeenEnergy434 pool w f) :=
      mul_le_mul_of_nonneg_left htotal hdelta
    _ = _ := by ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalNumericSeenFourierLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 9000000

variable {X R : Type} [Fintype X] [Fintype R] [AddCommGroup R]

/-- Fourier conjugation on the complete residue space, retaining the
entire active/history future in each frequency. -/
def sourceOriginalNumericSeenFourierLift434
    (op : AddChar R ℂ → (X → Finset ℕ → ℂ) → X → Finset ℕ → ℂ)
    (f : X → Finset ℕ → R → ℂ) (x : X) (S : Finset ℕ) : R → ℂ :=
  (AddChar.complexBasis R).equivFun.symm (fun psi =>
    op psi (fun y T => (AddChar.complexBasis R).equivFun (f y T) psi) x S)

/-- Parseval for the same joint density and true numerical histories.
The exact residue cardinal is present on both sides, with no loss. -/
theorem source_original_NUMERIC_SEEN_fourier_energy434
    (pool : Finset ℕ) (w : X → ℝ) (f : X → Finset ℕ → R → ℂ) :
    (∑ r : R,sourceOriginalNumericSeenEnergy434 pool w (fun x S => f x S r)) =
    (Fintype.card R:ℝ) * ∑ psi : AddChar R ℂ,
      sourceOriginalNumericSeenEnergy434 pool w
        (fun x S => (AddChar.complexBasis R).equivFun (f x S) psi) := by
  unfold sourceOriginalNumericSeenEnergy434
  have hp (x : X) (S : Finset ℕ) :
      (∑ r : R,‖f x S r‖^2) = (Fintype.card R:ℝ) *
        ∑ psi : AddChar R ℂ,‖(AddChar.complexBasis R).equivFun (f x S) psi‖^2 := by
    simpa only [Module.Basis.equivFun_apply] using source_original_B26_full_fourier_energy434 (f x S)
  calc
    _ = ∑ S ∈ pool.powerset,∑ x : X,w x*(∑ r : R,‖f x S r‖^2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ S ∈ pool.powerset,∑ x : X,w x*((Fintype.card R:ℝ) *
        ∑ psi : AddChar R ℂ,‖(AddChar.complexBasis R).equivFun (f x S) psi‖^2) := by
      simp_rw [hp]
    _ = _ := by
      simp only [Finset.mul_sum]
      trans ∑ S ∈ pool.powerset,∑ psi : AddChar R ℂ,∑ x : X,
        (Fintype.card R:ℝ)*(w x*‖(AddChar.complexBasis R).equivFun (f x S) psi‖^2)
      · apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro psi hpsi
        apply Finset.sum_congr rfl
        intro x hx
        ring
      · exact Finset.sum_comm

/-- A uniform spectral bound lifts to the whole frozen residue group,
without a number-of-frequencies loss and without a bounded future mask. -/
theorem source_original_NUMERIC_SEEN_FOURIER_spectral_lift434
    (pool : Finset ℕ) (w : X → ℝ) (delta : ℝ)
    (op : AddChar R ℂ → (X → Finset ℕ → ℂ) → X → Finset ℕ → ℂ)
    (hOp : ∀ psi g,sourceOriginalNumericSeenEnergy434 pool w (op psi g) ≤
      delta*sourceOriginalNumericSeenEnergy434 pool w g)
    (f : X → Finset ℕ → R → ℂ) :
    (∑ r : R,sourceOriginalNumericSeenEnergy434 pool w
      (fun x S => sourceOriginalNumericSeenFourierLift434 op f x S r)) ≤
    delta * ∑ r : R,sourceOriginalNumericSeenEnergy434 pool w (fun x S => f x S r) := by
  let cf := fun (psi : AddChar R ℂ) (x : X) (S : Finset ℕ) =>
    (AddChar.complexBasis R).equivFun (f x S) psi
  have he (psi : AddChar R ℂ) :
      (fun x S => (AddChar.complexBasis R).equivFun
        (sourceOriginalNumericSeenFourierLift434 op f x S) psi) = op psi (cf psi) := by
    funext x S
    exact congrFun ((AddChar.complexBasis R).equivFun.apply_symm_apply _) psi
  rw [source_original_NUMERIC_SEEN_fourier_energy434]
  simp_rw [he]
  calc
    _ ≤ (Fintype.card R:ℝ) * ∑ psi : AddChar R ℂ,
        delta*sourceOriginalNumericSeenEnergy434 pool w (cf psi) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun psi _ => hOp psi (cf psi)))
        (Nat.cast_nonneg _)
    _ = delta*((Fintype.card R:ℝ) * ∑ psi : AddChar R ℂ,
        sourceOriginalNumericSeenEnergy434 pool w (cf psi)) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      exact (source_original_NUMERIC_SEEN_fourier_energy434 pool w f).symm

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalNumericFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sourceOriginalB26NumericSharedSign434
    {G : Type} [Fintype G] [DecidableEq G]
    (nsmall J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m) (epsSrc epsTgt : Bool) : ℂ :=
  let shared := nsmall*J + ∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ nu g).card
  (if epsSrc then (-1:ℂ)^shared else 1)*(if epsTgt then (-1:ℂ)^shared else 1)

section Family
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (data : SourceComparisonData434 ι G cfg x L Y Hprime)
variable (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
variable (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
variable (c : SourceOriginalProbePattern434 G m → ℕ)
variable (theta : SourceOriginalProbePattern434 G m → ℝ)
variable (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
variable (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
variable (epsSrc epsTgt : Bool)
local notation "BP" => fun g : G => {p : ℕ // p ∈ data.Tb g}
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Nu" => SourceOriginalProbePattern434 G m

/-- The coherent sum of the EXISTING numeric CLEAN comparison-error
rows in the ACTUAL physical tilted active density. Each pattern uses
its own true free-target history update and both endpoint permutations.
All four independent shared endpoint signs are explicit. -/
def sourceOriginalB26NumericComparisonFamily434
    (f : A → Finset ℕ → ℂ) (s : A) (S : Finset ℕ) : ℂ :=
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
    sourceOriginalB26NumericPermutedClean434 BP (fun _ p => p.val) J ell m hmJ nu
      mu (sigma nu) (tau nu)
      (fun a _ b => sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig
        J ell m hmJ nu Q (hA nu) (hB nu) xi (c nu) a b
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta (theta nu) (orientation nu) k)
      f s S

/-- Finite coherent lifting of the genuine physical tilted B26
comparison pairing, with no change of density between steps. The
arithmetic all-pattern theorem supplies hPair in the next module.
The only extra factor is the number of probe patterns. -/
theorem source_original_B26_NUMERIC_COMPARISON_family_energy434
    (hmu : ∀ g (p : BP g),0 ≤ physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig g p)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPair : ∀ (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ), 0 ≤ ET →
      (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26ActiveEnergy434 BP J ell
          (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) (V nu) ≤ ET) →
      ‖∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
        sourceOriginalB26TiltedPermutedFullPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu‖^2 ≤
      delta * sourceOriginalB26ActiveEnergy434 BP J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) U * ET)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
      (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig)
      (sourceOriginalB26NumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f) ≤
    (delta*((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ)) *
      sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) f := by
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let w := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let value := fun nu : Nu => fun s t : A =>
    sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig J ell m hmJ nu Q
      (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
  let birth := fun nu : Nu => fun t : A =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
      (fun p : Sigma BP => p.2.val)
  let gate := fun s : A => fun S : Finset ℕ =>
    (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  let row := fun _S : Finset ℕ => fun nu : Nu => fun s t : A =>
    sign nu * sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) * value nu s t
  have hb (nu : Nu) (_ : nu ∈ family) (t : A) :
      birth nu t ⊆ sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨a.2,Finset.mem_univ _,rfl⟩⟩
  have hw (s : A) : 0 ≤ w s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have he :
      sourceOriginalB26NumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f =
      sourceOriginalNumericSeenFamilyLift434 family birth gate row f := by
    funext s S
    unfold sourceOriginalB26NumericComparisonFamily434 sourceOriginalNumericSeenFamilyLift434
    dsimp only
    by_cases hs : gate s S
    · simp only [if_pos hs]
      unfold sourceOriginalB26NumericPermutedClean434
      dsimp only [gate] at hs
      simp only [if_pos hs]
      apply Finset.sum_congr rfl
      intro nu hnu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [row,value,sign,birth,mu]
      split_ifs <;> simp [sourceOriginalB26CanonicalComparisonValue434,
        sourceOriginalB26CanonicalSharedDivisor434,
        sourceOriginalB26EndpointPermutationEquiv434,mul_assoc]
    · unfold sourceOriginalB26NumericPermutedClean434
      dsimp only [gate] at hs
      simp [gate,hs]
  rw [he]
  apply source_original_NUMERIC_SEEN_family_bilinear_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val)) family w hw
    birth hb gate row delta hdelta
  intro S hS U V ET hET hcap
  have hh := hPair U V ET hET hcap
  have hp :
      (∑ nu ∈ family,∑ s : A,(w s:ℂ)*star (U s)*(∑ t : A,row S nu s t*V nu t)) =
      ∑ nu ∈ family,sign nu *
        sourceOriginalB26TiltedPermutedFullPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu := by
    unfold sourceOriginalB26TiltedPermutedFullPairing434
    dsimp only [row,w,value,mu,sourceOriginalBigRefreshMass434]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro nu hnu
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hp]
  exact hh

end Family
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalNumericComparison -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine coherent all-pattern comparison ERROR on the physical
tilted active times numerical-seen space, at the original source depth.
Both endpoint permutations and all four shared signs remain explicit.
The future is arbitrary and may couple all active primes to the entire
history. No history-count loss or pointwise bound on the future occurs.

Only the polynomial number of probe patterns is charged. Its exponent
is chosen before the conductor and mesh; the threshold precedes J and
all moving source data. Auxiliary-ban, SMALL/OLD/Fock lifting and the
full RAW contribution are not asserted by this comparison-error bound. -/
theorem eventually_source_original_B26_PHYSICAL_NUMERIC_ALL_NU_COMPARISON_ERROR434
    (cfg : SourceComparisonFixed434) (ell : ℕ)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (J : ℕ) (hmJ : m ≤ J)
      (ζ : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<c ν)
      (hOrientation : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation ν=1 ∨ orientation ν= -1)
      (hZeta : |ζ| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
        (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal) * sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu f := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) cfg.hC0) hlog2
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_TILTED_HOMOGENEOUS_COMPARISON434
      cfg ell gamma dscale (Bgoal+E) Cfreq Ck hgamma hd (add_nonneg hGoal hE) hCk
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hMain hVisit hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ q hq hq1 sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ ζ k c theta orientation
    hDivisor hOrientation hZeta hk sigma tau epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let delta := L^(-(Bgoal+E))
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hh]
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast (data.hTbPrime g p.val p.property).pos
    exact one_div_pos.mpr (mul_pos (mul_pos
      (cfg.hv.trans_le (data.hVbig g)) hp) (hb g p))
  have hEnergy (U : A → ℂ) :
      0 ≤ sourceOriginalB26ActiveEnergy434 BP J ell mu U :=
    source_original_B26_active_energy_nonneg434 BP J ell mu hmu U
  have hAll (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ) (hET : 0 ≤ ET)
      (hcap : ∀ nu ∈ family,sourceOriginalB26ActiveEnergy434 BP J ell mu (V nu) ≤ ET) :=
    hMain x Y Hprime data q hq hq1 sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hDisjoint m hm J hmJ ζ k c theta orientation
      hDivisor hOrientation hZeta hk sigma tau
      (sourceOriginalB26ActiveEnergy434 BP J ell mu U) ET (hEnergy U) hET
      (fun _ => U) V
      (fun nu _ => ⟨hEnergy U,le_rfl⟩)
      (fun nu hnu => ⟨hEnergy (V nu),hcap nu hnu⟩) epsSrc epsTgt
  have hModes := (hAll (fun _ => 0) (fun _ _ => 0) 0 (le_refl _)
    (by intro nu hnu; simp [sourceOriginalB26ActiveEnergy434])).1
  refine ⟨hModes,?_⟩
  have hBound := source_original_B26_NUMERIC_COMPARISON_family_energy434
    data q N blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
    c theta orientation k sigma tau epsSrc epsTgt (fun g p => (hmu g p).le)
    delta hdelta (fun U V ET hET hcap => (hAll U V ET hET hcap).2) f
  have hCardNat : blockA.card+blockB.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_univ _
  have hCardReal : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) := by
    exact_mod_cast hCardNat
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L :=
    hCardReal.trans data.hBigGroups
  have hPower := source_original_probe_two_power_log_bound434
    blockA blockB m L cfg.C0 hL hGroups
  have hCount : (family.card:ℝ) ≤ (2:ℝ)^(m*(blockA.card+blockB.card)) := by
    exact_mod_cast source_original_two_block_probe_pattern_card434 blockA blockB m
  have hExp : (m:ℝ)*cfg.C0*Real.log 2 ≤ E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) cfg.hC0) hlog2
  have hCard : (family.card:ℝ) ≤ L^E :=
    hCount.trans (hPower.trans (Real.rpow_le_rpow_of_exponent_le hL hExp))
  have hBudget : delta*(family.card:ℝ) ≤ L^(-Bgoal) := by
    calc
      _ ≤ delta*L^E := mul_le_mul_of_nonneg_left hCard hdelta
      _ = L^(-Bgoal) := by
        dsimp only [delta]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  have hInput : 0 ≤ sourceOriginalB26NumericActiveEnergy434
      BP (fun _ p => p.val) J ell mu f := by
    exact Finset.sum_nonneg (fun S _ => hEnergy (fun s => f s S))
  exact hBound.trans (mul_le_mul_of_nonneg_right hBudget hInput)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NumericAuxBanFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

section Family
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (data : SourceComparisonData434 ι G cfg x L Y Hprime)
variable [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
variable (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
variable (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
variable (c : SourceOriginalProbePattern434 G m → ℕ)
variable (theta : SourceOriginalProbePattern434 G m → ℝ)
variable (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
variable (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
variable (epsSrc epsTgt : Bool)
local notation "BP" => fun g : G => {p : ℕ // p ∈ data.Tb g}
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Nu" => SourceOriginalProbePattern434 G m

/-- The literal auxiliary/ACTIVE ban correction with actual numerical
inventory and pattern-dependent fresh target history updates. -/
def sourceOriginalB26NumericAuxBanFamily434
    (f : A → Finset ℕ → ℂ) (s : A) (S : Finset ℕ) : ℂ :=
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (let birth := (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)
         if Disjoint S birth then
          sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu Q
            (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k * f t (S∪birth)
         else 0)
  else 0

/-- The genuine tilted auxiliary-ban pairing lifts to numerical seen.
The arithmetic premise is discharged by the next module. There is no
history-count cost and no bound on the modulus of the future. -/
theorem source_original_B26_NUMERIC_AUX_BAN_family_energy434
    (hmu : ∀ g (p : BP g),0 ≤ physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig g p)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPair : ∀ (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ), 0 ≤ ET →
      (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26ActiveEnergy434 BP J ell
          (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) (V nu) ≤ ET) →
      ‖∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
        sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu‖^2 ≤
      delta * sourceOriginalB26ActiveEnergy434 BP J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) U * ET)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
      (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig)
      (sourceOriginalB26NumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f) ≤
    (delta*((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ)) *
      sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) f := by
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let w := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let value := fun nu : Nu => fun s t : A =>
    sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu Q
      (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
  let birth := fun nu : Nu => fun t : A =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
      (fun p : Sigma BP => p.2.val)
  let gate := fun s : A => fun S : Finset ℕ =>
    (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  let row := fun _S : Finset ℕ => fun nu : Nu => fun s t : A =>
    sign nu * sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) * value nu s t
  have hb (nu : Nu) (_ : nu ∈ family) (t : A) :
      birth nu t ⊆ sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨a.2,Finset.mem_univ _,rfl⟩⟩
  have hw (s : A) : 0 ≤ w s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have he :
      sourceOriginalB26NumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f =
      sourceOriginalNumericSeenFamilyLift434 family birth gate row f := by
    funext s S
    unfold sourceOriginalB26NumericAuxBanFamily434 sourceOriginalNumericSeenFamilyLift434
    dsimp only
    by_cases hs : gate s S
    · dsimp only [gate] at hs
      simp only [gate,if_pos hs,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nu hnu
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [row,value,sign,birth,mu]
      split_ifs <;> simp [mul_assoc]
    · dsimp only [gate] at hs
      simp only [gate,if_neg hs]
  rw [he]
  apply source_original_NUMERIC_SEEN_family_bilinear_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val)) family w hw
    birth hb gate row delta hdelta
  intro S hS U V ET hET hcap
  have hh := hPair U V ET hET hcap
  have hp :
      (∑ nu ∈ family,∑ s : A,(w s:ℂ)*star (U s)*(∑ t : A,row S nu s t*V nu t)) =
      ∑ nu ∈ family,sign nu *
        sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu := by
    unfold sourceOriginalB26TiltedPermutedAuxBanPairing434
    dsimp only [row,w,value,mu,sourceOriginalBigRefreshMass434]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro nu hnu
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hp]
  exact hh

end Family
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalNumericAuxBan -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The actual auxiliary/ACTIVE ban has arbitrary-power energy saving
on physical tilted active primes times numerical seen, at original N.
Both permutations, all probe signs and arbitrary coupled futures remain.
The polynomial slot hypothesis is explicit and precedes no hidden limit. -/
theorem eventually_source_original_B26_PHYSICAL_NUMERIC_ALL_NU_AUX_BAN434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Cslots Bgoal : ℝ) (Cq Cxi : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (J m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (zeta : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (ho : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation nu=1 ∨ orientation nu= -1)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
        (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu f := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  let Ct := sourceOriginalB26TiltDensityExponent434 ell cfg.tmax cfg.C0
  let Dper : ℝ := Bgoal/2+3*E/2+Ct
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_canonical_aux_ban_saving434
    cfg.cexp cfg.vmin ((cfg.tmax:ℝ)*cfg.C0) Cslots Dper Cq Cxi
    hc cfg.hv (mul_nonneg (Nat.cast_nonneg _) cfg.hC0),
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hSave hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data instNZ q hq hq1
    hVbig hTbLower blockA blockB hBlocks J m hmJ hm hSlots Q hA hB xi
    hhA hhB hxi hQ hXi zeta k c theta orientation ho sigma tau epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let delta := L^(-Dper)
  let per := delta^2*(L^Ct)^2
  let total := (family.card:ℝ)^2*per
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hper : 0 ≤ per := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have htotal : 0 ≤ total := mul_nonneg (sq_nonneg _) hper
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val) q N g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 N g p (hVisit p.val (hTbLower g p.val p.property))).1
  have hb0 (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := hb g p
    linarith only [hh]
  have hVpos (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hVEq (g : G) : data.Vbig g = ∑ p : BP g,1/(p.val:ℝ) := by
    rw [hVbig]
    simpa [BP] using (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).symm
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hVpos g)
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb0 g p))
  have hGroups : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hnat : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hnat :
      ((blockA.card+blockB.card:ℕ):ℝ) ≤ (Fintype.card G:ℝ)).trans data.hBigGroups
  have hPattern (nu : Nu) (hnu : nu ∈ family) :
      ((nu.1.card+nu.2.card:ℕ):ℝ) ≤ ((cfg.tmax:ℝ)*cfg.C0)*Real.log L := by
    have hmem := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hnu
    have hNA : nu.1.card ≤ blockA.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.1
    have hNB : nu.2.card ≤ blockB.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.2.2
    have hNat : nu.1.card+nu.2.card ≤ m*(blockA.card+blockB.card) := by nlinarith only [hNA,hNB]
    calc
      _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by exact_mod_cast hNat
      _ ≤ (m:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg _)
      _ ≤ (cfg.tmax:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm)
          (mul_nonneg cfg.hC0 (Real.log_nonneg hL))
      _ = _ := by ring
  have hPair (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ) (hET : 0 ≤ ET)
      (hcap : ∀ nu ∈ family,sourceOriginalB26ActiveEnergy434 BP J ell mu (V nu) ≤ ET) :
      ‖∑ nu ∈ family,sign nu *
        sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q
          (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k sigma tau
          (fun _ => U) V nu‖^2 ≤
      total*sourceOriginalB26ActiveEnergy434 BP J ell mu U*ET := by
    let EU := sourceOriginalB26ActiveEnergy434 BP J ell mu U
    have hEU : 0 ≤ EU := source_original_B26_active_energy_nonneg434 BP J ell mu hmu U
    let pair := fun nu : Nu => sourceOriginalB26TiltedPermutedAuxBanPairing434
      data q N J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k
      sigma tau (fun _ => U) V nu
    have hPer (nu : Nu) (hnu : nu ∈ family) :
        ‖pair nu‖^2 ≤ per*EU*sourceOriginalB26ActiveEnergy434 BP J ell mu (V nu) := by
      apply source_original_B26_physical_tilt_uniform_bilinear434
        BP (fun _ p => p.val) q N data.Vbig hVpos hVEq hb
        J ell m cfg.tmax hmJ hm nu (sigma nu) (tau nu) cfg.C0 L hL data.hBigGroups
        delta hdelta U (V nu)
      intro s t
      exact hSave data.Tb data.Vbig J ell m hmJ nu
        (source_original_probe_memory_actual_pattern_disjoint434 blockA blockB hBlocks m nu hnu)
        Q hA hB xi hhA hhB hxi hVbig data.hVbig hTbLower (hPattern nu hnu)
        hSlots hQ hXi (c nu) s t (sigma nu) (tau nu)
        zeta (theta nu) (orientation nu) k (ho nu hnu)
    have hEach (nu : Nu) (hnu : nu ∈ family) :
        ‖sign nu*pair nu‖^2 ≤ (1:ℝ)^2*(per*EU*ET) := by
      have hs : ‖sign nu‖=1 := by
        dsimp only [sign,sourceOriginalB26NumericSharedSign434]
        rw [norm_mul]
        split_ifs <;> simp
      rw [norm_mul,hs,one_mul,one_pow,one_mul]
      exact (hPer nu hnu).trans
        (mul_le_mul_of_nonneg_left (hcap nu hnu) (mul_nonneg hper hEU))
    have hh := source_original_true_finite_weighted_minor_square434
      family (fun nu => sign nu*pair nu) (fun _ => (1:ℝ)) (per*EU*ET)
      (mul_nonneg (mul_nonneg hper hEU) hET) (by intro nu hnu;norm_num) hEach
    have hh' : ‖∑ nu ∈ family,sign nu*pair nu‖^2 ≤
        (family.card:ℝ)^2*(per*EU*ET) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
    calc
      _ ≤ (family.card:ℝ)^2*(per*EU*ET) := hh'
      _ = _ := by dsimp only [total];ring
  have hBound := source_original_B26_NUMERIC_AUX_BAN_family_energy434
    data q N blockA blockB J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta
    c theta orientation k sigma tau epsSrc epsTgt (fun g p => (hmu g p).le)
    total htotal hPair f
  have hmE : (m:ℝ)*cfg.C0*Real.log 2 ≤ E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0)
      (Real.log_nonneg (by norm_num))
  have hCard : (family.card:ℝ) ≤ L^E :=
    (source_original_probe_family_log_power_card434 blockA blockB m L cfg.C0 hL hGroups).trans
      (Real.rpow_le_rpow_of_exponent_le hL hmE)
  have hBudget : total*(family.card:ℝ) ≤ L^(-Bgoal) := by
    calc
      _ ≤ ((L^E)^2*per)*L^E :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hCard 2) hper)
          hCard (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _) hper)
      _ = L^(-Bgoal) := by
        dsimp only [per,delta]
        rw [← Real.rpow_two,← Real.rpow_two,← Real.rpow_two,
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,
          ← Real.rpow_add hLp,← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        dsimp only [Dper]
        ring
  have hInput : 0 ≤ sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu f :=
    Finset.sum_nonneg (fun S _ =>
      source_original_B26_active_energy_nonneg434 BP J ell mu hmu (fun s => f s S))
  exact hBound.trans (mul_le_mul_of_nonneg_right hBudget hInput)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26ResidueComparisonValue -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Original RAW divisor with SMALL/shared factors and both free products. -/
def sourceOriginalB26CanonicalRawDivisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) : ℕ :=
  sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ nu dsmall s sigma *
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ nu
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu
        (fun g i => t g (tau g i))) *
     sourceOriginalProbeFreeSourceX434 J ell m hmJ nu
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu
        (fun g i => s g (sigma g i))))

/-- Literal unbanned auxiliary evolution minus its signed RAW term.
Every summand uses its OWN full divisor in the simultaneous SMALL/OLD
residue translation. No averaged divisor or bounded future is used. -/
def sourceOriginalB26ResidueComparisonValue434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    (F : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime → ℂ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  (∑ aux : SourceBigAux BP J m pat,
    (sourceAuxMass BP (fun _ p => p.val) J m V pat aux:ℂ) *
      (originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        zeta theta
        (sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall pat aux s sigma) o k *
       F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime
        (o*k*(sourceOriginalB26FrozenD434 BP (fun _ p => p.val)
          J ell m dsmall pat aux s sigma:ℤ))))) -
  originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta
    (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau) o k *
    F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime
      (o*k*(sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
        dsmall s t sigma tau:ℤ)))

/-- Exact Fourier identity for auxiliary-minus-RAW residue evolution.
The same frequency shift acts on the two different original divisors,
with the genuine joint RAW/comparison multiplier unchanged. -/
theorem source_original_B26_RESIDUE_COMPARISON_FOURIER434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) (hDisj : Disjoint nu.1 nu.2)
    (F : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime → ℂ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
    sourceOriginalB26ResidueComparisonValue434 SP sm P V J ell m hmJ nu sizes prime
      Q hA hB xi dsmall s t sigma tau zeta theta o k F r =
    ∑ psi : AddChar Torus ℂ,
      sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ nu
        Q hA hB xi dsmall s t sigma tau zeta
        (theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ p => p.val) sizes prime psi/
          (2*Real.pi)) o k *
      (AddChar.complexBasis Torus).equivFun F psi * psi r := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  let Aux := SourceBigAux BP J m pat
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let angle := fun psi : AddChar Torus ℂ =>
    theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ p => p.val) sizes prime psi/
      (2*Real.pi)
  let weight := fun aux : Aux => (sourceAuxMass BP (fun _ p => p.val) J m V pat aux:ℂ)
  let kval := fun aux : Aux =>
    sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux
      (fun g i => s g (sigma g i)) (fun g i => t g (tau g i))
  let divisor := fun aux : Aux =>
    sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall pat aux s sigma
  let draw := sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau
  let rawK := -((-1:ℂ)^(nu.1.card+nu.2.card))
  have hShift (K : ℂ) (D : ℕ) :
      originalEdgeScalar K zeta theta D o k *
        F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime (o*k*(D:ℤ))) =
      ∑ psi : AddChar Torus ℂ,originalEdgeScalar K zeta (angle psi) D o k *
        (AddChar.complexBasis Torus).equivFun F psi * psi r := by
    have hs := memory_frozen_full_residue_fourier_shift_formula
      SP sm BP (fun _ p => p.val) sizes prime (o*k*(D:ℤ)) F r
    dsimp only at hs
    rw [hs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro psi hpsi
    dsimp only [angle]
    rw [← source_original_B26_FROZEN_scalar_frequency434]
    simp only [Module.Basis.equivFun_apply]
    ring
  change (∑ aux : Aux,weight aux*(originalEdgeScalar (kval aux) zeta theta
      (divisor aux) o k * F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val)
        sizes prime (o*k*(divisor aux:ℤ))))) -
    originalEdgeScalar rawK zeta theta draw o k *
      F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val)
        sizes prime (o*k*(draw:ℤ))) = _
  simp_rw [hShift]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro psi hpsi
  have hc := source_original_B26_unbanned_scalar_comparison434 P V J ell m hmJ nu hDisj
    Q hA hB xi dsmall s t sigma tau zeta (angle psi) o k
  change (∑ aux : Aux,weight aux*originalEdgeScalar (kval aux) zeta (angle psi)
    (divisor aux) o k) - originalEdgeScalar rawK zeta (angle psi) draw o k =
    sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ nu Q hA hB xi
      dsmall s t sigma tau zeta (angle psi) o k at hc
  calc
    _ = ((∑ aux : Aux,weight aux*originalEdgeScalar (kval aux) zeta (angle psi)
        (divisor aux) o k) - originalEdgeScalar rawK zeta (angle psi) draw o k) *
        (AddChar.complexBasis Torus).equivFun F psi * psi r := by
      simp only [sub_mul,Finset.sum_mul,mul_assoc]
    _ = _ := by rw [hc]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NumericResidueFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Original auxiliary-minus-RAW evolution with coherent probe signs,
physical tilted fresh law, both endpoint permutations, full source-D
residue translations and the exact numerical no-rebirth update. -/
def sourceOriginalB26NumericResidueComparisonFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell)
    (S : Finset ℕ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)) then
          sourceOriginalB26ResidueComparisonValue434 SP sm data.Tb data.Vbig J ell m hmJ nu
            sizes prime Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k
            (f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
                (fun p : Sigma BP => p.2.val))) r
         else 0)
  else 0

/-- Exact all-frequency identity on the same active times seen carrier.
No sum is taken over histories, and the auxiliary divisor remains inside
its physical translation until the proved scalar Fourier identity is used. -/
theorem source_original_B26_NUMERIC_RESIDUE_COMPARISON_FOURIER434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (hBlocks : Disjoint blockA blockB)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NumericResidueComparisonFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    sourceOriginalNumericSeenFourierLift434
      (fun psi => sourceOriginalB26NumericComparisonFamily434 data q N blockA blockB
        J ell m hmJ Q hA hB xi zeta c
        (fun nu => theta nu+sourceOriginalB26ModeAngle434 SP sm
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ => Subtype.val) sizes prime psi/(2*Real.pi))
        orientation k sigma tau epsSrc epsTgt) f := by
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let angle := fun (psi : AddChar Torus ℂ) (nu : Nu) =>
    theta nu+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi)
  let birth := fun (nu : Nu) (t : A) =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
        (fun p : Sigma BP => p.2.val)
  let law := fun (nu : Nu) (s t : A) =>
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu)
  let value := fun (psi : AddChar Torus ℂ) (nu : Nu) (s t : A) =>
    sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig J ell m hmJ nu
      Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
      zeta (angle psi nu) (orientation nu) k
  funext s S r
  unfold sourceOriginalNumericSeenFourierLift434
  simp only [Module.Basis.equivFun_symm_apply,AddChar.complexBasis_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases hs : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  · dsimp only [BP] at hs
    have hterm (nu : Nu) (hnu : nu ∈ family) (t : A) :
        (if Disjoint S (birth nu t) then
          sourceOriginalB26ResidueComparisonValue434 SP sm data.Tb data.Vbig
            J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
            s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
            (f t (S∪birth nu t)) r else 0) =
        ∑ psi : AddChar Torus ℂ,
          (if Disjoint S (birth nu t) then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r := by
      by_cases hb : Disjoint S (birth nu t)
      · simp only [if_pos hb]
        exact source_original_B26_RESIDUE_COMPARISON_FOURIER434
          SP sm data.Tb data.Vbig J ell m hmJ nu sizes prime
          Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
          zeta (theta nu) (orientation nu) k
          (source_original_probe_memory_actual_pattern_disjoint434 blockA blockB hBlocks m nu hnu)
          (f t (S∪birth nu t)) r
      · simp [hb]
    have hcore (psi : AddChar Torus ℂ) :
        sourceOriginalB26NumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S =
        ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (if Disjoint S (birth nu t) then value psi nu s t *
            (AddChar.complexBasis Torus).equivFun (f t (S∪birth nu t)) psi else 0) := by
      unfold sourceOriginalB26NumericComparisonFamily434 sourceOriginalB26NumericPermutedClean434
      dsimp only
      simp only [if_pos hs]
      apply Finset.sum_congr rfl
      intro nu hnu
      congr 1
    change sourceOriginalB26NumericResidueComparisonFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k sigma tau
      epsSrc epsTgt f s S r =
      ∑ psi : AddChar Torus ℂ,
        sourceOriginalB26NumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S * psi r
    simp_rw [hcore]
    unfold sourceOriginalB26NumericResidueComparisonFamily434
    dsimp only
    rw [if_pos hs]
    change (∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
      (if Disjoint S (birth nu t) then
        sourceOriginalB26ResidueComparisonValue434 SP sm data.Tb data.Vbig
          J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
          s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
          (f t (S∪birth nu t)) r else 0)) = _
    calc
      _ = ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (∑ psi : AddChar Torus ℂ,(if Disjoint S (birth nu t) then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [hterm nu hnu t]
      _ = _ := by
        simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
        trans ∑ nu ∈ family,∑ psi : AddChar Torus ℂ,∑ t : A,
          sign nu*(law nu s t*((if Disjoint S (birth nu t) then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r))
        · apply Finset.sum_congr rfl
          intro nu hnu
          exact Finset.sum_comm
        · exact Finset.sum_comm
  · dsimp only [BP] at hs
    simp [sourceOriginalB26NumericResidueComparisonFamily434,
      sourceOriginalB26NumericComparisonFamily434,sourceOriginalB26NumericPermutedClean434,hs]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26ResidueAuxBanValue -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Literal discarded auxiliary/ACTIVE mass, with each original full
divisor retained inside its own SMALL/OLD residue translation. -/
def sourceOriginalB26ResidueAuxBanValue434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    (F : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime → ℂ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  ∑ aux : SourceBigAux BP J m pat,
    (sourceAuxMass BP (fun _ p => p.val) J m V pat aux:ℂ) *
      (if sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux s t then 0 else
       originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        zeta theta
        (sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall pat aux s sigma) o k *
       F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime
        (o*k*(sourceOriginalB26FrozenD434 BP (fun _ p => p.val)
          J ell m dsmall pat aux s sigma:ℤ))))

/-- The actual allowed auxiliary residue evolution minus its canonical
RAW contribution. Both auxiliary/ACTIVE exclusion and RAW signs remain. -/
def sourceOriginalB26ResidueCleanRawValue434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    (F : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime → ℂ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  (∑ aux : SourceBigAux BP J m pat,
    (sourceAuxMass BP (fun _ p => p.val) J m V pat aux:ℂ) *
      (if sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux s t then
       originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        zeta theta
        (sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall pat aux s sigma) o k *
       F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime
        (o*k*(sourceOriginalB26FrozenD434 BP (fun _ p => p.val)
          J ell m dsmall pat aux s sigma:ℤ)))
       else 0)) -
  originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta
    (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau) o k *
    F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime
      (o*k*(sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
        dsmall s t sigma tau:ℤ)))

/-- Exact complete-residue Fourier expansion of the true ban correction.
The mask stays inside the auxiliary sum; no averaged divisor is used. -/
theorem source_original_B26_RESIDUE_AUX_BAN_FOURIER434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    (F : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime → ℂ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
    sourceOriginalB26ResidueAuxBanValue434 SP sm P V J ell m hmJ nu sizes prime
      Q hA hB xi dsmall s t sigma tau zeta theta o k F r =
    ∑ psi : AddChar Torus ℂ,
      sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ nu
        Q hA hB xi dsmall s t sigma tau zeta
        (theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ p => p.val) sizes prime psi/
          (2*Real.pi)) o k *
      (AddChar.complexBasis Torus).equivFun F psi * psi r := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  let Aux := SourceBigAux BP J m pat
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let angle := fun psi : AddChar Torus ℂ =>
    theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ p => p.val) sizes prime psi/
      (2*Real.pi)
  let weight := fun aux : Aux => (sourceAuxMass BP (fun _ p => p.val) J m V pat aux:ℂ)
  let ban := fun aux : Aux => sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux s t
  let kval := fun aux : Aux =>
    sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux
      (fun g i => s g (sigma g i)) (fun g i => t g (tau g i))
  let divisor := fun aux : Aux =>
    sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall pat aux s sigma
  have hShift (K : ℂ) (D : ℕ) :
      originalEdgeScalar K zeta theta D o k *
        F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime (o*k*(D:ℤ))) =
      ∑ psi : AddChar Torus ℂ,originalEdgeScalar K zeta (angle psi) D o k *
        (AddChar.complexBasis Torus).equivFun F psi * psi r := by
    have hs := memory_frozen_full_residue_fourier_shift_formula
      SP sm BP (fun _ p => p.val) sizes prime (o*k*(D:ℤ)) F r
    dsimp only at hs
    rw [hs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro psi hpsi
    dsimp only [angle]
    rw [← source_original_B26_FROZEN_scalar_frequency434]
    simp only [Module.Basis.equivFun_apply]
    ring
  have hAux (aux : Aux) :
      weight aux*(if ban aux then 0 else originalEdgeScalar (kval aux) zeta theta
        (divisor aux) o k * F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val)
          sizes prime (o*k*(divisor aux:ℤ)))) =
      ∑ psi : AddChar Torus ℂ,
        (weight aux*(if ban aux then 0 else
          originalEdgeScalar (kval aux) zeta (angle psi) (divisor aux) o k)) *
        (AddChar.complexBasis Torus).equivFun F psi * psi r := by
    by_cases hb : ban aux
    · simp [hb]
    · simp only [if_neg hb]
      rw [hShift,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro psi hpsi
      ring
  change (∑ aux : Aux,weight aux*(if ban aux then 0 else
      originalEdgeScalar (kval aux) zeta theta (divisor aux) o k *
      F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val)
        sizes prime (o*k*(divisor aux:ℤ))))) = _
  simp_rw [hAux]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi hpsi
  change (∑ aux : Aux,(weight aux*(if ban aux then 0 else
      originalEdgeScalar (kval aux) zeta (angle psi) (divisor aux) o k)) *
        (AddChar.complexBasis Torus).equivFun F psi * psi r) =
    (∑ aux : Aux,weight aux*(if ban aux then 0 else
      originalEdgeScalar (kval aux) zeta (angle psi) (divisor aux) o k)) *
        (AddChar.complexBasis Torus).equivFun F psi * psi r
  simp only [Finset.sum_mul]

/-- Literal allowed-minus-RAW equals comparison error minus the actual
discarded auxiliary/ACTIVE contribution, for the same coupled future. -/
theorem source_original_B26_RESIDUE_CLEAN_RAW_DECOMPOSITION434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    (F : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime → ℂ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ => Subtype.val) sizes prime) :
    sourceOriginalB26ResidueCleanRawValue434 SP sm P V J ell m hmJ nu sizes prime
      Q hA hB xi dsmall s t sigma tau zeta theta o k F r =
    sourceOriginalB26ResidueComparisonValue434 SP sm P V J ell m hmJ nu sizes prime
      Q hA hB xi dsmall s t sigma tau zeta theta o k F r -
    sourceOriginalB26ResidueAuxBanValue434 SP sm P V J ell m hmJ nu sizes prime
      Q hA hB xi dsmall s t sigma tau zeta theta o k F r := by
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  let Aux := SourceBigAux BP J m pat
  let weight := fun aux : Aux => (sourceAuxMass BP (fun _ p => p.val) J m V pat aux:ℂ)
  let ban := fun aux : Aux => sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux s t
  let val := fun aux : Aux =>
    originalEdgeScalar
      (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux
        (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
      zeta theta
      (sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall pat aux s sigma) o k *
    F (r+memoryFrozenResidueShift SP sm BP (fun _ p => p.val) sizes prime
      (o*k*(sourceOriginalB26FrozenD434 BP (fun _ p => p.val)
        J ell m dsmall pat aux s sigma:ℤ)))
  have hs : (∑ aux : Aux,weight aux*val aux) =
      (∑ aux : Aux,weight aux*(if ban aux then val aux else 0)) +
      (∑ aux : Aux,weight aux*(if ban aux then 0 else val aux)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro aux haux
    by_cases hb : ban aux <;> simp [hb]
  unfold sourceOriginalB26ResidueCleanRawValue434 sourceOriginalB26ResidueComparisonValue434
    sourceOriginalB26ResidueAuxBanValue434
  dsimp only
  change (∑ aux : Aux,weight aux*(if ban aux then val aux else 0)) - _ =
    ((∑ aux : Aux,weight aux*val aux) - _) -
      (∑ aux : Aux,weight aux*(if ban aux then 0 else val aux))
  rw [hs]
  ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NumericResidueAuxBanFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Original auxiliary/ACTIVE ban correction with coherent probe signs,
physical tilted fresh law, both endpoint permutations, full source-D
residue translations and the exact numerical no-rebirth update. -/
def sourceOriginalB26NumericResidueAuxBanFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell)
    (S : Finset ℕ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)) then
          sourceOriginalB26ResidueAuxBanValue434 SP sm data.Tb data.Vbig J ell m hmJ nu
            sizes prime Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k
            (f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
                (fun p : Sigma BP => p.2.val))) r
         else 0)
  else 0

/-- Exact all-frequency identity on the same active times seen carrier.
No sum is taken over histories, and the auxiliary divisor remains inside
its physical translation until the proved scalar Fourier identity is used. -/
theorem source_original_B26_NUMERIC_RESIDUE_AUX_BAN_FOURIER434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NumericResidueAuxBanFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    sourceOriginalNumericSeenFourierLift434
      (fun psi => sourceOriginalB26NumericAuxBanFamily434 data q N blockA blockB
        J ell m hmJ Q hA hB xi zeta c
        (fun nu => theta nu+sourceOriginalB26ModeAngle434 SP sm
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ => Subtype.val) sizes prime psi/(2*Real.pi))
        orientation k sigma tau epsSrc epsTgt) f := by
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let angle := fun (psi : AddChar Torus ℂ) (nu : Nu) =>
    theta nu+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi)
  let birth := fun (nu : Nu) (t : A) =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
        (fun p : Sigma BP => p.2.val)
  let law := fun (nu : Nu) (s t : A) =>
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu)
  let value := fun (psi : AddChar Torus ℂ) (nu : Nu) (s t : A) =>
    sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu
      Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
      zeta (angle psi nu) (orientation nu) k
  funext s S r
  unfold sourceOriginalNumericSeenFourierLift434
  simp only [Module.Basis.equivFun_symm_apply,AddChar.complexBasis_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases hs : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  · dsimp only [BP] at hs
    have hterm (nu : Nu) (hnu : nu ∈ family) (t : A) :
        (if Disjoint S (birth nu t) then
          sourceOriginalB26ResidueAuxBanValue434 SP sm data.Tb data.Vbig
            J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
            s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
            (f t (S∪birth nu t)) r else 0) =
        ∑ psi : AddChar Torus ℂ,
          (if Disjoint S (birth nu t) then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r := by
      by_cases hb : Disjoint S (birth nu t)
      · simp only [if_pos hb]
        exact source_original_B26_RESIDUE_AUX_BAN_FOURIER434
          SP sm data.Tb data.Vbig J ell m hmJ nu sizes prime
          Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
          zeta (theta nu) (orientation nu) k
          (f t (S∪birth nu t)) r
      · simp [hb]
    have hcore (psi : AddChar Torus ℂ) :
        sourceOriginalB26NumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S =
        ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (if Disjoint S (birth nu t) then value psi nu s t *
            (AddChar.complexBasis Torus).equivFun (f t (S∪birth nu t)) psi else 0) := by
      dsimp only [sourceOriginalB26NumericAuxBanFamily434]
      rw [if_pos hs]
    change sourceOriginalB26NumericResidueAuxBanFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k sigma tau
      epsSrc epsTgt f s S r =
      ∑ psi : AddChar Torus ℂ,
        sourceOriginalB26NumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S * psi r
    simp_rw [hcore]
    unfold sourceOriginalB26NumericResidueAuxBanFamily434
    dsimp only
    rw [if_pos hs]
    change (∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
      (if Disjoint S (birth nu t) then
        sourceOriginalB26ResidueAuxBanValue434 SP sm data.Tb data.Vbig
          J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
          s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
          (f t (S∪birth nu t)) r else 0)) = _
    calc
      _ = ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (∑ psi : AddChar Torus ℂ,(if Disjoint S (birth nu t) then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [hterm nu hnu t]
      _ = _ := by
        simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
        trans ∑ nu ∈ family,∑ psi : AddChar Torus ℂ,∑ t : A,
          sign nu*(law nu s t*((if Disjoint S (birth nu t) then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r))
        · apply Finset.sum_congr rfl
          intro nu hnu
          exact Finset.sum_comm
        · exact Finset.sum_comm
  · dsimp only [BP] at hs
    simp [sourceOriginalB26NumericResidueAuxBanFamily434,
      sourceOriginalB26NumericAuxBanFamily434,hs]


/-- Literal allowed auxiliary evolution minus RAW on numerical seen. -/
def sourceOriginalB26NumericResidueCleanRawFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell)
    (S : Finset ℕ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)) then
          sourceOriginalB26ResidueCleanRawValue434 SP sm data.Tb data.Vbig J ell m hmJ nu
            sizes prime Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k
            (f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
                (fun p : Sigma BP => p.2.val))) r
         else 0)
  else 0


/-- Exact comparison-minus-ban decomposition on the same coupled future,
with coherent signs and every actual pattern-dependent history update. -/
theorem source_original_B26_NUMERIC_RESIDUE_CLEAN_RAW_DECOMPOSITION434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NumericResidueCleanRawFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    fun s S r =>
      sourceOriginalB26NumericResidueComparisonFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f s S r -
      sourceOriginalB26NumericResidueAuxBanFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f s S r := by
  classical
  funext s S r
  unfold sourceOriginalB26NumericResidueCleanRawFamily434
    sourceOriginalB26NumericResidueComparisonFamily434 sourceOriginalB26NumericResidueAuxBanFamily434
  dsimp only
  split_ifs with hs
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro nu hnu
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← mul_sub]
    congr 1
    split_ifs <;> simp only [source_original_B26_RESIDUE_CLEAN_RAW_DECOMPOSITION434,sub_self]
  · simp

end Green64Analytic.CorrelationSquare

end

end

