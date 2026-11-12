module

public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part001
public import Green64.Library.OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part037
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part014
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssemblyHigh -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (dyadCost : ℝ) (hdyadCost : 0<dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0<sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+sigma≤7/1200)
    (hcentral : sigma+nu+dyadCost≤ saving) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∃C : ℝ,
      0<C ∧
    ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤C0 →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (HeckeZeroSupremum.beta-7/8)
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0<dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith)
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  have hΔ : 0≤HeckeZeroSupremum.beta-7/8 := by linarith
  have hΔ1 : HeckeZeroSupremum.beta-7/8≤1/8 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨C,hC,hbound⟩ :=
    actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (HeckeZeroSupremum.beta-7/8) ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤1 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(3/16+(HeckeZeroSupremum.beta-7/8)-saving+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum

end SevenEighths.ProbeFinalAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssemblyFixedHigh -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : (7/8:ℝ)<HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-7/8)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.cost)
    (hτt : τ<D.t) (hτ2 : 2*τ≤D.t) (hτeps : τ*(2+4*D.eps)<D.t) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,0≤C0 → SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta-11/16-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (13/16:ℝ)+D.t+2*D.t≤7/8 := by linarith
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) D.t ht (by linarith) (by positivity) D.count_budget (by nlinarith [D.central_budget])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le
    D.sigma D.sigma_pos D.geometric_budget D.principal_budget D.window_budget D.floor_budget D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (13/16+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤Z^(13/16+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ)<51/100+D.e*j := by
    have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j≤1 := by simpa only [huj] using (hbins u).2.1
  have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm v ∧
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
      rowNorm v≤Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
  have hi' : (i:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ≤Z^(2*τ) := by
    have hZp : 0<Z := zero_lt_one.trans hZ
    calc
      _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _≤Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end SevenEighths.ProbeFinalAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssembly -/

section

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem common_probe_of_raw_moments (hmom : RawMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  have hgap : 0<HeckeZeroSupremum.beta-7/8 := by linarith
  obtain ⟨D⟩ := exists_high_data (HeckeZeroSupremum.beta-7/8) hgap
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := raw_input_chosen_height hmom hβ D F counts
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hlossgap : loss<HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_raw_moments (hmom : RawMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_raw_moments hmom) q hq χ s hs hexc

theorem zeta_of_raw_moments (hmom : RawMomentInput) (s : ℂ) (hs : (7/8:ℝ)<s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_raw_moments hmom) s hs

theorem hecke_of_raw_moments (hmom : RawMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_raw_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssemblyChosenData -/

section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

def ChosenMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
    ∃D:HighData (HeckeZeroSupremum.beta-7/8),∃F:SourceData D,
    ∃counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
    ∃mesh:ℝ→ℝ,(∀t:ℝ,0<t→0< mesh t) ∧
    ∀D:HighData (HeckeZeroSupremum.beta-7/8),(∀j,D.ell j≤ mesh D.t/200)→
    ∀F:SourceData D,∀counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h:FineMomentInput):ChosenMomentInput:=by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩:=h hβ
  obtain ⟨D,hD⟩:=exists_high_data_fine (HeckeZeroSupremum.beta-7/8) (by linarith) mesh hmesh
  obtain ⟨F⟩:=exists_source_data D
  obtain ⟨counts⟩:=source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0≤J)
    (hbound:∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
    ∃τ:ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200)*D.cost ∧ τ<D.t ∧
      2*τ≤D.t ∧ τ*(2+4*D.eps)<D.t ∧
      ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ≤1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem common_probe_of_chosen_moments (hmom : ChosenMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩:=hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hlossgap : loss<HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_chosen_moments (hmom : ChosenMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_chosen_moments hmom) q hq χ s hs hexc

theorem zeta_of_chosen_moments (hmom : ChosenMomentInput) (s : ℂ) (hs : (7/8:ℝ)<s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_chosen_moments hmom) s hs

theorem hecke_of_chosen_moments (hmom : ChosenMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_chosen_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField
local notation "O"=>HeckeFamily.O

def detectorMesh (Δ t:ℝ):ℝ:=fineMesh 2 0 1 (3/4+2*Δ) (t/4)

lemma detectorMesh_pos {Δ t:ℝ}(hΔ:0<Δ)(ht:0<t):0<detectorMesh Δ t:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (3/4+2*Δ) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith) (by positivity)).2.2.2.2.1

def DetectorCertifiedBands:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
  ∀D:HighData (HeckeZeroSupremum.beta-7/8),
    (∀j,D.ell j≤detectorMesh (HeckeZeroSupremum.beta-7/8) D.t/200)→
  ∀F:SourceData D,∀bΦ:ℝ,0<bΦ→
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D))

theorem plain_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (hcert:∀bΦ:ℝ,0<bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D) (count 2 (stageError D))):
    PositiveFineSourceInput F (detectorMesh Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters D
  have ht (bΦ:ℝ)(hbΦ:0<bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0<bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (detectorMesh Δ D.t) (33/50) (33/50) 2
        (stageError D) (kappaPlain D) U η₀ (sourceFixedIdeal F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal F)
      (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=>h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=>h.1)⟩

theorem source_moments {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j≤ mesh/200)
    (hpositive:PositiveFineSourceInput F mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=ProbeDetectorInverseFields.source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine F mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0<Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0≤height:=Real.rpow_nonneg hZ.le _
  have hbase:1≤1+height:=by linarith
  have hCi':Ci*(1+height)^Ji≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

theorem fine_moments_of_certified (h:DetectorCertifiedBands):FineMomentInput:=by
  intro hβ
  let Δ:=HeckeZeroSupremum.beta-7/8
  have hΔ:0<Δ:=by dsimp [Δ];linarith
  refine ⟨detectorMesh Δ,fun t ht=>detectorMesh_pos hΔ ht,?_⟩
  intro D hfine F counts
  obtain ⟨hp,hz⟩:=plain_inputs F (h hβ D hfine F)
  exact source_moments F counts (detectorMesh Δ D.t) (detectorMesh_pos hΔ D.t_pos) hfine hp hz

theorem chosen_moments_of_certified (h:DetectorCertifiedBands):ChosenMomentInput:=
  chosen_input_of_fine (fine_moments_of_certified h)

theorem dirichlet_of_certified (h:DetectorCertifiedBands)(q:ℕ)(hq:q≠0)
    (χ:DirichletCharacter ℂ q)(s:ℂ)(hs:(7/8:ℝ)<s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_chosen_moments (chosen_moments_of_certified h) q hq χ s hs hexc

theorem zeta_of_certified (h:DetectorCertifiedBands)(s:ℂ)(hs:(7/8:ℝ)<s.re):riemannZeta s≠0:=
  zeta_of_chosen_moments (chosen_moments_of_certified h) s hs

end SevenEighths.ProbeFinalAssemblyCertifiedBands

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace SevenEighths.ProbeFinalAssemblyUnconditional
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

theorem detector_certified_bands:DetectorCertifiedBands:=by
  intro hβ D _hfine F bΦ hbΦ
  have hp:=fixed_parameters D
  apply terminal_certificate (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

theorem dirichlet_nonzero (q:ℕ)(hq:q≠0)(χ:DirichletCharacter ℂ q)(s:ℂ)
    (hs:(7/8:ℝ)<s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_certified detector_certified_bands q hq χ s hs hexc

theorem zeta_nonzero (s:ℂ)(hs:(7/8:ℝ)<s.re):riemannZeta s≠0:=
  zeta_of_certified detector_certified_bands s hs

end SevenEighths.ProbeFinalAssemblyUnconditional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Nonvanishing -/

section

namespace OAI

/-!
# Nonvanishing of Dirichlet L-functions to the right of seven eighths

The main result excludes zeros of Dirichlet L-functions in the half-plane
`7 / 8 < re s`, apart from the principal character's pole at `s = 1`.
The corresponding nonvanishing statement for the Riemann zeta function follows.
-/

namespace DirichletCharacter
open scoped _root_.DirichletCharacter

/-- Dirichlet L-functions do not vanish to the right of `7 / 8`, away from the
principal character's pole at `1`. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
    q (NeZero.ne q) χ s hs hpole

end DirichletCharacter

/-- The Riemann zeta function does not vanish to the right of `7 / 8`. -/
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero s hs

end OAI

end

