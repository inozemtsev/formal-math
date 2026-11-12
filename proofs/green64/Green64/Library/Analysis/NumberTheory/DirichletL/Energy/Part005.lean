module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part034
public import Green64.Library.OAI.NumberTheory.DirichletL.Energy.WidthFloor
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part013

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.WidthInduction -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

def remaining (M ε:ℝ)(k:ℕ):ℕ:=count M ε-k
def lowerAt (a b M ε:ℝ)(k:ℕ):ℝ:=CenteredMomentEnergyProfiles.lower a b (remaining M ε k)
def lengthAt (M B L ε:ℝ)(k:ℕ):ℝ:=range M B L (remaining M ε k)

lemma lowerAt_pos (a b M ε:ℝ)(ha:0<a)(k:ℕ):0<lowerAt a b M ε k:=
  CenteredMomentEnergyProfiles.lower_pos a b ha _

lemma child_support (a b M ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lowerAt a b M ε k=lowerAt a b M ε (k+1)/max 1 b:=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lowerAt,he,CenteredMomentEnergyProfiles.lower]

lemma child_length (M B L ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lengthAt M B L ε k=step M B (lengthAt M B L ε (k+1)):=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lengthAt,he,range]

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (width Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (width Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0<a)(hb:0≤b)(hrad:0< radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ0:0≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have ha0:=lowerAt_pos a b Mcap ε ha 0
  obtain ⟨degree,S,Czero,Cpositive,hCzero,hCpositive,hfloor⟩:=
    actual_joint_floor (α:=α) M H hH Mcap Bs κ ε hMcap hBs hκ0 hε W aslot bslot
      haslot hWs hW (lowerAt a b Mcap ε 0) b radial Bmask (lengthAt Mcap Bmask L ε 0)
      lo hi ha0 hb hrad hmask hbeta hκ
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM _ _ _
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hfloor η₀] with Z hZ
  have hh:=hZ.2 Q hQM
  have hloss:loss Mcap Bs ε 0≤ stageLoss Mcap Bs ε 0:=by
    unfold stageLoss
    linarith
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      le_rfl le_rfl hloss le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hh.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hloss le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hh.2

omit [Fintype α] [DecidableEq α] in
theorem certified_terminal (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  obtain ⟨hs,hs1,hse,hr,hm,hmm,hκm,h20,hcover,hloss⟩:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have he:stageLoss Mcap Bs ε (count Mcap ε)≤ε:=by
    have hh:=stageLoss_final Mcap Bs κ ε hMcap hBs hκ0 hε (count Mcap ε) le_rfl
    linarith
  obtain ⟨degree,S,hbound⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCzero,hCpositive,hcert⟩:=hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hcert] with Z hZ
  have hz:=hZ.2.1
  have hp:=hZ.2.2
  simp only [lowerAt,lengthAt,remaining,Nat.sub_self,CenteredMomentEnergyProfiles.lower,range] at hz hp
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) hcover.le he le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hz
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl (le_max_right _ _) hcover.le he le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hp

end SevenEighths.CenteredMomentEnergyWidthInduction

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

def bandWidth (M B ε:ℝ)(k:ℕ):ℝ:=min M (width M B ε k)
lemma bandWidth_le (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤M:=min_le_left _ _
lemma bandWidth_le_schedule (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤width M B ε k:=min_le_right _ _
lemma bandWidth_nonneg (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)(k:ℕ):
    0≤bandWidth M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.1
  have hs:0<amplification ε:=(bounds M B 0 ε hM hB (by norm_num) hε).1
  unfold bandWidth width
  positivity
lemma bandWidth_terminal (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε):
    bandWidth M B ε (count M ε)=M:=by
  have hh: M<width M B ε (count M ε):=
    (bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.2.2.2.2.2.1
  exact min_eq_left hh.le
lemma actual_child_band (M B ε parent child:ℝ)(hε:0<ε)(k:ℕ)
    (hp:parent≤bandWidth M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤bandWidth M B ε k:=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  apply le_min
  · have hh:=hp.trans (bandWidth_le M B ε (k+1));linarith
  · exact child_band M B ε parent child k (hp.trans (bandWidth_le_schedule M B ε (k+1))) hc

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0<a)(hb:0≤b)(hrad:0< radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ0:0≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have ha0:=lowerAt_pos a b Mcap ε ha 0
  obtain ⟨degree,S,Czero,Cpositive,hCzero,hCpositive,hfloor⟩:=
    actual_joint_floor (α:=α) M H hH Mcap Bs κ ε hMcap hBs hκ0 hε W aslot bslot
      haslot hWs hW (lowerAt a b Mcap ε 0) b radial Bmask (lengthAt Mcap Bmask L ε 0)
      lo hi ha0 hb hrad hmask hbeta hκ
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM _ _ _
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hfloor η₀] with Z hZ
  have hh:=hZ.2 Q hQM
  have hloss:loss Mcap Bs ε 0≤ stageLoss Mcap Bs ε 0:=by
    unfold stageLoss
    linarith
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hh.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hh.2

omit [Fintype α] [DecidableEq α] in
theorem certified_terminal (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  obtain ⟨hs,hs1,hse,hr,hm,hmm,hκm,h20,hcover,hloss⟩:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have he:stageLoss Mcap Bs ε (count Mcap ε)≤ε:=by
    have hh:=stageLoss_final Mcap Bs κ ε hMcap hBs hκ0 hε (count Mcap ε) le_rfl
    linarith
  obtain ⟨degree,S,hbound⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCzero,hCpositive,hcert⟩:=hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hcert] with Z hZ
  have hz:=hZ.2.1
  have hp:=hZ.2.2
  simp only [lowerAt,lengthAt,remaining,Nat.sub_self,CenteredMomentEnergyProfiles.lower,range] at hz hp
  have hterminal:=bandWidth_terminal Mcap Bs ε hMcap hBs hε
  change bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (count Mcap ε)=Mcap at hterminal
  rw [hterminal] at hz hp
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hz
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hp

end SevenEighths.CenteredMomentEnergyCappedWidthInduction

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CappedBandTransport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedBandTransport
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma saturated_successor (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (hsaturated:bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k=Mcap)
    (h:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε k):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0< reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hwidth:bandWidth Mcap Bs ε (k+1)≤bandWidth Mcap Bs ε k:=by
    rw [hsaturated]
    exact bandWidth_le _ _ _ _
  have hloss:stageLoss Mcap Bs ε k≤ stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨degree,S,hcert⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCz,hCp,hbound⟩:=hcert η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCz,hCp,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le hlower le_rfl le_rfl le_rfl
      hlength hwidth hloss le_rfl (Finset.Subset.refl _) hCz.le le_rfl hZ.2.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      hlower le_rfl le_rfl le_rfl hlength hwidth hloss le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hZ.2.2

end SevenEighths.CenteredMomentEnergyCappedBandTransport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport -/

section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedRadialTransport
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyBandMonotonicity
local notation "O" => HeckeFamily.O
variable {α : Type*}
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem certified_radial_mono (W : ℝ → ℂ)
    (bslot a b radialOld radialNew Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (hrad : radialNew ≤ radialOld)
    (h : CertifiedBand (α := α) M H hH W bslot a b radialOld Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH W bslot a b radialNew Bmask L lo hi Mcap κ ε k := by
  obtain ⟨degree, S, hbound⟩ := h
  refine ⟨degree, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero, Cpositive, hCzero, hCpositive, hcert⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero, Cpositive, hCzero, hCpositive, ?_⟩
  filter_upwards [hcert] with Z hZ
  refine ⟨hZ.1, ?_, ?_⟩
  · exact zeroAt_transport _ _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl hrad le_rfl
      le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hZ.2.1
  · exact positiveAt_transport (α := α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl hrad le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hZ.2.2

theorem certified_from_max_two (W : ℝ → ℂ)
    (bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (h : CertifiedBand (α := α) M H hH W bslot a b (max 2 radial)
      Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k :=
  certified_radial_mono (α := α) M H hH W bslot a b (max 2 radial) radial
    Bmask L lo hi Mcap κ ε k (le_max_right _ _) h

end SevenEighths.CenteredMomentEnergyCappedRadialTransport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowth
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands QuadraticInitialBound
local notation "O" => HeckeFamily.O

def ZeroGrowthAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = Q → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ,
    0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.plainEnergy p t X₁ X₂ ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + ‖t‖) ^ degree *
        Z ^ (max s.width (length Z X₁ + length Z X₂) + ε)

lemma zeroGrowth_of_zeroAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ZeroAt Q a b bΦ Bmask L M ε Z degree S C) :
    ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  apply (h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
  have he : s.width + ε ≤ max s.width (length Z X₁ + length Z X₂) + ε := by
    linarith [le_max_left s.width (length Z X₁ + length Z X₂)]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one he)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC
    (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _)

lemma zeroGrowth_on_capacity (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (h : ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = Q) (hs : s.width ≤ M)
    (p : Profiles a b) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hcapacity : length Z X₁ + length Z X₂ ≤ s.width) :
    s.plainEnergy p t X₁ X₂ ≤ C * diagonalControl s.radial.profile *
      (p.control S) ^ 2 * (1 + ‖t‖) ^ degree * Z ^ (s.width + ε) := by
  simpa only [max_eq_left hcapacity] using
    h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂

theorem exists_zero_growth_floor (a b bΦ Bmask L ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hbΦ : 0 < bΦ) (hmask : 0 ≤ Bmask)
    (hε : 0 < ε) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Q : Ideal O, ∀ Z : ℝ, 1 ≤ Z →
        ZeroGrowthAt Q a b bΦ Bmask L (ε / 16) ε Z degree S C := by
  obtain ⟨degree, S, C, hC, hf⟩ := exists_zero_floor a b bΦ Bmask ε ha hb hbΦ hmask hε
  refine ⟨degree, S, C, hC, ?_⟩
  intro Q Z hZ
  exact zeroGrowth_of_zeroAt Q a b bΦ Bmask L (ε / 16) ε Z degree S C hC.le
    (zeroAt_of_zeroBound Q a b bΦ Bmask L (ε / 16) ε Z 1 degree S C (hf Q) hZ)

end SevenEighths.CenteredMomentEnergyZeroGrowth

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceChild -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

lemma independent_energy {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (hB:0≤Bmask)(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    (unitBudgetState s hB).plainEnergy (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂:=by
  have hh:=independent_child_energy s ha W₁ W₂ hs₁ hs₂ (∅:Finset (Fin 0))
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t₁ t₂ X₁ X₂ hX₁ hX₂ (by simp)
  simpa only [Finset.prod_empty,mul_one,energy,NaturalState.plainEnergy,
    CenteredMomentRetainedEnergy.positiveSlotRow,Fintype.prod_empty,
    unitBudgetState,unpuncturedState,NaturalState.mask,effectiveState,effectiveRadial] using hh

theorem independent_from_low
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hsmall:length Z X₁+length Z X₂≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(s.width+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_low
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hsmall:length Z X₁+length Z X₂≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(s.width+ε):=by
  have hh:=independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end SevenEighths.CenteredMomentEnergyZeroReferenceChild

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthChild -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

theorem independent_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    :
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    :
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  have hh:=independent_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthChild

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroReferenceGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
local notation "O"=>HeckeFamily.O

lemma low_or_reflected (M short along xi:ℝ)(hM:0≤M)(hs:short≤M/4)(_hxi:0≤xi)
    (hxiM:xi≤M/6):
    max 0 short+max 0 along≤5*M/6 ∨
      (0<along ∧ max 0 (M-along+xi)+max 0 short≤5*M/6):=by
  have hs0:max 0 short≤M/4:=max_le (by linarith) hs
  by_cases hl:max 0 short+max 0 along≤5*M/6
  · exact Or.inl hl
  · right
    have halong:0<along:=by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn)] at hl
      linarith
    refine ⟨halong,?_⟩
    rw [max_eq_right halong.le] at hl
    rcases le_total 0 (M-along+xi) with hh|hh
    · rw [max_eq_right hh]
      linarith
    · rw [max_eq_left hh]
      linarith

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hxi:0≤xi)(hxiM:xi≤ s.width/6)
    (hlarge:s.width/4≤Real.logb Z (X₁*X₂))
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤L ∧ -Bmask≤along ∧
    s.width≤Mcap+Bmask+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((along≤L ∧ length Z (Z^short)+length Z (Z^along)≤5*s.width/6) ∨
      (0<along ∧ max 0 (s.width-along+xi)+length Z (Z^short)≤5*s.width/6)):=by
  dsimp only
  have hZ0:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁
  have hl₂:=Real.logb_nonneg hZ hn₂
  have hu₂:Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn₂)).mpr hc₂
  have hM:=s.width_nonneg
  have hL0:0≤L:=by linarith
  have he₁:Z^(s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ))=
      comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ):=by
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' (zero_lt_one.trans_le hn₁)]
    rfl
  have he₂:Z^(Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ))=
      comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
    rw [Real.rpow_sub hZ0,Real.rpow_sub hZ0,
      Real.rpow_logb hZ0 hZ.ne' (mul_pos hX₁ hX₂),
      Real.rpow_logb hZ0 hZ.ne' (zero_lt_one.trans_le hn₂)]
    rfl
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,by linarith,
    max_le hL0 (by linarith),?_⟩
  have hlen (v:ℝ):length Z (Z^v)=max 0 v:=by
    rcases le_total 0 v with hv|hv
    · rw [length, max_eq_right (Real.one_le_rpow hZ.le hv),
        Real.logb_rpow hZ0 hZ.ne',max_eq_right hv]
    · rw [length,max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le hv),
        Real.logb_one,max_eq_left hv]
  simp only [hlen]
  rcases low_or_reflected s.width
    (s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ))
    (Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ))
    xi hM (by linarith) hxi hxiM with hd|hr
  · refine Or.inl ⟨?_,hd⟩
    have hh₁:=le_max_right (0:ℝ)
      (Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ))
    have hh₂:=le_max_left (0:ℝ) (s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ))
    linarith
  · exact Or.inr hr

end SevenEighths.CenteredMomentEnergyZeroReferenceGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceMoments -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroReferenceChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    length Z X₁+length Z X₂≤5*s.width/6 →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hh:=reflected_from_low a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroReferenceMoments

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyZeroReferenceMoments CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
local notation "O"=>HeckeFamily.O

theorem reference_from_low
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask L Mcap ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K → 0≤Bmask →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+ε);
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t)
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=reflected_uniform a b ha hlo hhi S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap ε Q degree K hK hlow hBmask s hQ hs
    Wlong Wshort hsLong hsShort t along bshort hlength hL hbshort hsmall
  dsimp only
  have hh:=hZ.2 Bmask s Wlong Wshort hsLong hsShort (Fin 0) ∅
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t along bshort
    (K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+ε)) hlength
  simp only [Finset.prod_empty,mul_one] at hh
  apply hh
  · have hz:0<Z:=zero_lt_one.trans hZ.1
    have hd:0≤diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
    positivity
  · intro v j k x hx
    have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
    exact hchild bΦ Bmask L Mcap ε Z Q degree K hK hlow hBmask s hQ hs Wshort hsShort
      j k v t (Real.exp x) (Z^bshort) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
      (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hL))
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbshort)
      (by linarith [hwindow.1])

end SevenEighths.CenteredMomentEnergyZeroReferenceReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceDeleted -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyZeroReferenceGeometry CenteredMomentEnergyZeroReferenceReflection
open CenteredMomentEnergyZeroReferenceError CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
local notation "O"=>HeckeFamily.O

theorem deleted_from_low (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤ s.width/6 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀t X₁ X₂:ℝ,0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (comparisonFirst Z s.width/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (comparisonSecond Z s.width X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)):=by
  obtain ⟨Ce,hCe,he⟩:=short_energy_bound b
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Ce,hC,mul_pos hD hCe,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM W₁ W₂ hs₁ hs₂ t X₁ X₂ hX₁ hX₂ hlarge D₁ hD₁ D₂ hD₂
  let short:=s.width/4-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ xi hs hL
    hX₁ hX₂ hxi.le hxiM hlarge D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S K hlow hBmask ha
      s hQ hs W₁ W₂ hs₁ hs₂ t t (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hd.1) hd.2
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Mcap ε Q degree K hK hlow hBmask s hQ hs
      W₂ W₁ hs₂ hs₁ t along short hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2
    dsimp only at hh
    have he₁:=he W₁ (fun x hx=>(hs₁ hx).2) (fun z=>naturalCharacter s.character z)
      t (Z^short) s.radial.scale s.radial.profile (effectiveState s).radial.keep
      (Real.rpow_pos_of_pos hZpos _) s.radial.scale_pos s.radial.nonneg
    have hswap:(fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t)=
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · calc
        _≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          (Ce*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)):=by
          gcongr
          exact he₁.trans (by
            gcongr
            · exact hZ.1.le
            · exact hg.2.2.1)
        _=_:=by ring

end SevenEighths.CenteredMomentEnergyZeroReferenceDeleted

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceOriginal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroReferenceDeleted
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O

theorem original_from_low (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤ s.width/6 →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4))):=by
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_from_low
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hp:=comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith)
    (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
    t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) _ 0
  · simp
  · simp
  · simp
  · simp
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_zero] using
      hZ.2 ε Q degree K hK hlow s hQ hs hxiM (p.profile 0) (p.profile 1)
        (p.support 0) (p.support 1) t X₁ X₂ hX₁ hX₂ hlarge D₁ hD₁ D₂ hD₂

end SevenEighths.CenteredMomentEnergyZeroReferenceOriginal

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hxiM:xi≤ s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 e Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hledger:=hscalar e he Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyZeroReferenceBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceLiveBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLiveBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceBounded CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceLiveBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferencePower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePower
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hxiM:xi≤ s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 d Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hledger:=hscalar Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyZeroReferencePower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceLive -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLive
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePower CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤L ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceLive

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysical -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLive CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

def balancedInput {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):Input (Fin 0):=
  naturalInput s p ha (fun _=>∅) (by simp) (fun _=>s.character) (fun _=>0)
    (fun _=>1) (fun _=>1) (by simp) (by simp) 1 1 (by norm_num)
    (by simp) (by simp) t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂ (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

lemma balanced_volume {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    CenteredMomentAmplificationChildInput.volume (balancedInput s p ha t X₁ X₂ hX₁ hX₂)=X₁*X₂:=by
  simp only [CenteredMomentAmplificationChildInput.volume,
    balancedInput,naturalInput,completeInput,naturalData,Finset.univ_eq_empty,Finset.prod_empty,mul_one]

theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap d Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B →
      5*s.width/6≤length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 Q degree K hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤_+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysicalBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroReferencePhysical

theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B →
      5*s.width/6≤length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤_+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReflectionSupport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => HeckeFamily.O

def naturalDualScale (χ ψ : Character) (X : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)

lemma naturalDualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
    (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) :
    0<naturalDualScale χ ψ X D H := by
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    (Finset.mem_powerset.mp hD hP))
  have hH := norm_pos H.val
  unfold naturalDualScale
  positivity

theorem eventually_natural_choice_range (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      ∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY → 0≤M-a+xi := by
  filter_upwards [eventually_natural_choice_geometry C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod D hD H hY n hn
  have h := hZ.2 χ ψ M a hcap hmod ((⟨D,hD⟩,H),n) hY hn
  have hz := Real.log_pos hZ.1
  have hm : 0≤(M-a+xi)*Real.log Z := h.2.1.trans h.2.2
  nlinarith

theorem eventually_natural_source_zero (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M → M+xi<a →
      (∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H),
        retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅) ∧
      (∀(D : Finset (Ideal O)),D∈(redundantSet χ.modulus ψ.modulus).powerset →
        ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))(η : Character)(F : ℝ→ℂ),
        finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0) ∧
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  filter_upwards [eventually_natural_choice_range C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod hfar
  have hempty (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
      (hY : 0<naturalDualScale χ ψ (Z^a) D H) :
      retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := hZ.2 χ ψ M a hcap hmod D hD H hY n hn
    linarith
  have hcol (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) (η : Character)(F : ℝ→ℂ) :
      finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0 := by
    have hy := naturalDualScale_pos χ ψ (Z^a) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) D hD H
    rw [finiteAnnularColumn,dite_eq_left hy,hempty D hD H hy]
    simp
  refine ⟨hempty,hcol,?_,?_⟩
  · intro W t
    unfold retainedOriginal
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]
  · intro G
    unfold retainedSchwartz
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]

lemma deleted_short_length (Z b Xshort Xlong Nshort : ℝ)
    (hZ : 1<Z)(_hb : 0<b)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hN : 1≤Nshort)(hsupport : 1≤b*Xlong) :
    length Z (Xshort/Nshort)≤Real.logb Z Xlong+Real.logb Z (max 1 b) := by
  have hx : 0<Xlong := hshort.trans_le hlong
  have hn : 0<Nshort := zero_lt_one.trans_le hN
  have hd : Xshort/Nshort≤Xlong := (div_le_self hshort.le hN).trans hlong
  have hlog := Real.logb_le_logb_of_le hZ (div_pos hshort hn) hd
  have hprod : 1≤ max 1 b*Xlong := hsupport.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
  have hzero := Real.logb_nonneg hZ hprod
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left 1 b))) hx.ne'] at hzero
  rw [length_eq_max_log Z _ hZ (div_pos hshort hn)]
  apply max_le
  · linarith
  · exact hlog.trans (le_add_of_nonneg_right (Real.logb_nonneg hZ (le_max_left _ _)))

theorem live_deleted_growth (Z b M xi Xshort Xlong Nshort Nlong : ℝ)
    (hZ : 1<Z)(hb : 0<b)(_hM : 0≤M)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hNs : 1≤Nshort)(hNl : 1≤Nlong)(hsupport : 1≤b*Xlong)
    (hlive : 0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (x : ℝ)(hx : x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/Nshort)≤
      M+Real.logb Z Nlong+Real.logb Z (max 1 b)+xi := by
  have hxlong : 0<Xlong := hshort.trans_le hlong
  have hnlong : 0<Nlong := zero_lt_one.trans_le hNl
  have hwindow := (reflection_window_length Z _ x hZ (le_max_left _ _) hx).1
  rw [max_eq_right hlive,Real.logb_div hxlong.ne' hnlong.ne'] at hwindow
  have hshortbound := deleted_short_length Z b Xshort Xlong Nshort hZ hb hshort hlong hNs hsupport
  linarith

theorem eventually_endpoint_defect (b epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b)≤epsilon := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (max 1 b)/epsilon))] with Z hZ hz
  refine ⟨hZ,?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have hh := (div_le_iff₀ hepsilon).mp hz
  nlinarith

theorem actual_deleted_growth {Z Bmask bΦ : ℝ}(s : NaturalState Z Bmask bΦ)
    (b xi Xshort Xlong : ℝ)(hZ : 1<Z)(hb : 0<b)
    (hshort : 0<Xshort)(hlong : Xshort≤Xlong)(hsupport : 1≤b*Xlong)
    (Dshort Dlong : Finset (Ideal O))
    (hDs : Dshort∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hDl : Dlong∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hlive : 0≤ s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)
    (x : ℝ)(hx : x∈Set.Icc 0
      (max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
      s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+Real.logb Z (max 1 b)+xi := by
  exact live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ hb s.width_nonneg
    hshort hlong (divisor_norm s Dshort hDs).1 (divisor_norm s Dlong hDl).1 hsupport hlive x hx

theorem eventually_actual_source_zero (bΦ xi : ℝ)(hbΦ : 0<bΦ)(hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀a : ℝ,s.width+xi<a →
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_source_zero C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap a hfar
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  exact (hZ.2 (naturalCharacter s.character z) ψ s.width a hcap hm hfar).2.2

theorem eventually_actual_deleted_growth (b epsilon : ℝ)(hb : 0<b)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask bΦ : ℝ)(s : NaturalState Z Bmask bΦ)
      (xi Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      0≤ s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  filter_upwards [eventually_endpoint_defect b epsilon hepsilon] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask bΦ s xi Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl hlive x hx
  have h := actual_deleted_growth s b xi Xshort Xlong hZ.1 hb hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx
  linarith [hZ.2]

theorem eventually_actual_retained_deleted_growth (b bΦ xi epsilon : ℝ)
    (hb : 0<b)(hbΦ : 0<bΦ)(hxi : 0<xi)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀(Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      ∀(E : Finset (Ideal O)),E∈(redundantSet χ.modulus ψ.modulus).powerset →
      ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4))
        (naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H) hY →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_choice_range C xi hC hxi,
    eventually_actual_deleted_growth b epsilon hb hepsilon] with Z hZ hgrowth
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl E hE H hY n hn x hx
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hL : 0<Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    div_pos (hshort.trans_le hlong) (zero_lt_one.trans_le (divisor_norm s Dlong hDl).1)
  have hexp : Z^(Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))=
      Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    Real.rpow_logb (zero_lt_one.trans hZ.1) hZ.1.ne' hL
  have hrange := hZ.2 (naturalCharacter s.character z) ψ s.width
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))) hcap hm E hE H
  rw [hexp] at hrange
  have hlive := hrange hY n hn
  exact hgrowth.2 Bmask bΦ s xi Xshort Xlong hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthMoments -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroGrowthChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(max s.width (length Z X₁+length Z X₂)+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hh:=reflected_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(max s.width (length Z X₁+length Z X₂)+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

lemma actual_growth_power (Z b M xi epsilon loss Xshort Xlong Nshort Nlong x:ℝ)
    (hZ:1<Z)(hb:0<b)(hM:0≤M)(he:0≤epsilon)(hxi:0≤xi)
    (hshort:0<Xshort)(hlong:Xshort≤Xlong)(hNs:1≤Nshort)(hNl:1≤Nlong)
    (hsupport:1≤b*Xlong)(hdef:Real.logb Z (max 1 b)≤epsilon)
    (hlive:0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (hx:x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)):
    Z^(max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss)≤
      Nlong*Z^(M+loss+epsilon+xi):=by
  have hg:=live_deleted_growth Z b M xi Xshort Xlong Nshort Nlong
    hZ hb hM hshort hlong hNs hNl hsupport hlive x hx
  have hN:=Real.logb_nonneg hZ hNl
  have hemax:max M (length Z (Real.exp x)+length Z (Xshort/Nshort))≤
      M+Real.logb Z Nlong+epsilon+xi:=max_le (by linarith) (by linarith)
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le (show max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss≤M+Real.logb Z Nlong+epsilon+xi+loss by linarith)
  apply hp.trans_eq
  rw [show M+Real.logb Z Nlong+epsilon+xi+loss=
    Real.logb Z Nlong+(M+loss+epsilon+xi) by ring,
    Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans_le hNl)]

end SevenEighths.CenteredMomentEnergyZeroGrowthMoments

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthWindow -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthWindow
open CenteredMomentFiniteProfileExceptional
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthMoments CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow CenteredMomentEnergyReferenceLowBranchGeometry
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_reflected_window (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap loss Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S C→0≤Bmask→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀(Wshort:𝓢(ℝ,ℂ)),Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀xi epsilon Xshort Xlong:ℝ,0≤xi→0≤epsilon→1<Z→
    Real.logb Z (max 1 b)≤epsilon→Mcap+Bmask+epsilon+xi≤L→
    0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Nshort:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nlong:ℝ:=(∏P∈Dlong,P).absNorm;
    0≤ s.width-Real.logb Z (Xlong/Nlong)+xi→
    ∀(j k:Fin 2)(v t x:ℝ),
    x∈Set.Icc 0 (max 0 (s.width-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)→
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Xshort/Nshort) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+loss+epsilon+xi)*Nlong)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hu⟩:=reflected_uniform a b ha hlo hhi S
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    xi epsilon Xshort Xlong hxi he hZ hdef hL hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive j k v t x hx
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:0<((∏P∈Dshort,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
  have hpL:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hpL).mpr hNlcap
  have hlen:=live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ (by linarith)
    s.width_nonneg hshort hlong hNs hNl hsupport hlive x hx
  have hn:=length_nonneg Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ)) hZ
  have hlenx:length Z (Real.exp x)≤L:=by linarith
  have hlogx:Real.logb Z (Real.exp x)≤length Z (Real.exp x):=by
    rw [length_eq_max_log Z _ hZ (Real.exp_pos _)]
    exact le_max_right _ _
  have hxc:Real.exp x≤Z^L:=(Real.logb_le_iff_le_rpow hZ (Real.exp_pos _)).mp (hlogx.trans hlenx)
  have hsc:Xshort/((∏P∈Dshort,P).absNorm:ℝ)≤Z^L:=
    (div_le_self hshort.le hNs).trans hshortcap
  have hh:=hu bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    j k v t (Real.exp x) (Xshort/((∏P∈Dshort,P).absNorm:ℝ))
    (Real.exp_pos _) (div_pos hshort hpS) hxc hsc
  have hp:=actual_growth_power Z b s.width xi epsilon loss Xshort Xlong _ _ x
    hZ (by linarith) s.width_nonneg he hxi hshort hlong hNs hNl hsupport hdef hlive hx
  have hcoef:0≤C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*(1+|t|)^(2*n):=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  apply hh.trans
  have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hcoef)
    (show 0≤(1+‖v‖)^(2*n) by positivity)
  convert hbnd using 1 ; ring
end SevenEighths.CenteredMomentEnergyZeroGrowthWindow

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReflection
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

theorem live_deleted_reflection (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤ s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
          (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=actual_reflected_window a b ha hlo hhi S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hz:=zero_lt_one.trans hZ.1
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:=zero_lt_one.trans_le hNs
  have hpL:=zero_lt_one.trans_le hNl
  have hxl:=hshort.trans_le hlong
  have hlogs:=deleted_short_length Z b Xlong Xlong 1 hZ.1 (by linarith) hxl le_rfl le_rfl hsupport
  simp only [div_one] at hlogs
  have hn:=length_nonneg Z Xlong hZ.1
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ.1 hpL).mpr hNlcap
  have hlength:s.width≤Lreflect+Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)):=by
    rw [Real.logb_div hxl.ne' hpL.ne']
    linarith [hendpoint.2]
  have hpowL:=Real.rpow_logb hz hZ.1.ne' (div_pos hxl hpL)
  have hpowS:=Real.rpow_logb hz hZ.1.ne' (div_pos hshort hpS)
  let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*((∏P∈Dlong,P).absNorm:ℝ)
  have hh:=hZ.2 Bmask s Wlong Wshort hsLong hsShort (Fin 0) ∅
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))
    (Real.logb Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))) E hlength
  simp only [Finset.prod_empty,mul_one,hpowL,hpowS] at hh
  apply hh
  · dsimp [E]
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  · intro v j k x hx
    exact hchild bΦ Bmask L Mcap loss Z Q degree K hK hgrowth hBmask s hQ hs Wshort hsShort
      xi defect Xshort Xlong hxi.le hdefect.le hZ.1 hendpoint.2 hL
      hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive j k v t x hx
end SevenEighths.CenteredMomentEnergyZeroGrowthReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounds -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounds
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyZeroReferenceError CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma actual_window_cap (Z b Bmask bΦ Mcap defect xi L Xlong:ℝ)
    (hZ:1<Z)(hb:0<b)(hx:0<Xlong)(hsupport:1≤b*Xlong)
    (hdefect:Real.logb Z (max 1 b)≤defect)
    (hL:Mcap+Bmask+defect+xi≤L)(hL0:0≤L)
    (s:NaturalState Z Bmask bΦ)(hs:s.width≤Mcap)
    (Dlong:Finset (Ideal O))(hDl:Dlong∈(CompletedGauss.primeSupport s.puncture).powerset):
    max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)≤L:=by
  obtain ⟨hn,hncap⟩:=divisor_norm s Dlong hDl
  have hnp:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hnp).mpr hncap
  have hlow:=deleted_short_length Z b Xlong Xlong 1 hZ hb hx le_rfl le_rfl hsupport
  simp only [div_one] at hlow
  have hnon:=CenteredMomentEnergyBands.length_nonneg Z Xlong hZ
  apply max_le hL0
  rw [Real.logb_div hx.ne' hnp.ne']
  linarith

theorem actual_deleted_short_mass (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ L:ℝ)(s:NaturalState Z Bmask bΦ)
      (W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Iic b→
      ∀t X:ℝ,0<X→X≤Z^L→
      ∀D:Finset (Ideal O),D∈(CompletedGauss.primeSupport s.puncture).powerset→
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W
        (X/((∏P∈D,P).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L:=by
  obtain ⟨C,hC,hbound⟩:=short_energy_bound b
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ L s W hW t X hX hcap D hD
  obtain ⟨hn,_⟩:=divisor_norm s D hD
  have hnp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hh:=hbound W hW (naturalCharacter s.character) t
    (X/((∏P∈D,P).absNorm:ℝ)) s.radial.scale s.radial.profile
    (effectiveState s).radial.keep (div_pos hX hnp) s.radial.scale_pos s.radial.nonneg
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ((div_le_self hX.le hn).trans hcap)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (diagonalControl_nonneg _)) (le_max_of_le_left zero_le_one)

end SevenEighths.CenteredMomentEnergyZeroGrowthBounds

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounded
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyZeroGrowthReflection CenteredMomentEnergyZeroGrowthBounds

theorem live_deleted_bounded (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤ s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(L*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L :=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=live_deleted_reflection
    a b bΦ epsilon xi defect saving Lreflect ha hlo hhi hbΦ hepsilon hxi hdefect B hB S
  obtain ⟨Cshort,hCs,hshortmass⟩:=actual_deleted_short_mass b
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cshort,hC,mul_pos hD hCs,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive
  have hL0:0≤L:=by linarith [s.width_nonneg]
  have hw:=actual_window_cap Z b Bmask bΦ Mcap defect xi L Xlong hZ.1 (by linarith)
    (hshort.trans_le hlong) hsupport hendpoint.2 hL hL0 s hs Dlong hDl
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hwindow:1+2*(max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)
      ≤1+2*(L*Real.log Z):=by nlinarith
  have hmass:=hshortmass Z Bmask bΦ L s Wshort (fun x hx=>(hsShort hx).2)
    t Xshort hshort hshortcap Dshort hDs
  have hd:=diagonalControl_nonneg s.radial.profile
  have hN:0≤((∏P∈Dlong,P).absNorm:ℝ):=Nat.cast_nonneg _
  have hZ0:0<Z:=zero_lt_one.trans hZ.1
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hwindow (by positivity)
    · positivity
  · have he:=mul_le_mul_of_nonneg_left hmass
      (show 0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving) by positivity)
    convert he using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroGrowthBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroRetainedError -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalPrimitive CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyZeroReflectionSupport CenteredMomentOriginalRadialComparison
open CenteredMomentRadialPolynomialEnergy CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentEnergyReferenceReflection
local notation "O" => HeckeFamily.O

theorem finite_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀{ι : Type}[Fintype ι],∀χ : ι→Character,(∀i,(χ i).residue≠1) →
      ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
      ∀(G : ι→𝓢(ℝ,ℂ))(P : ι→ℂ)(Z M along Src Rcap : ℝ),Z₀≤Z →
        M+xi<along → 0<Src → 1≤Rcap →
        (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤Src) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
        (∀i,retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0) ∧
        (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*P i‖^2)≤
          C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,happrox⟩:=CenteredMomentUniformOriginalEnergy.actual_original_energy_to_retained
    (xi/2) saving 0 Cscale epsilon (by positivity) hscale hepsilon
  obtain ⟨Z₁,hZ₁⟩:=eventually_atTop.mp (eventually_natural_source_zero Cscale xi hscale hxi)
  refine ⟨H,C,max 2 Z₁,hC,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ι _ χ hχ
  obtain ⟨ψ,hψ,henergy⟩:=happrox χ hχ
  refine ⟨ψ,hψ,?_⟩
  intro G P Z M along Src Rcap hZ₀ hfar hSrc hR hGS hmod hcap
  have hZ:=hZ₁ Z ((le_max_right _ _).trans hZ₀)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hzero(i:ι):retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0:=
    (hZ.2 (χ i) (ψ i) M along (hψ i).2.2 (hmod i) hfar).2.2.2 (G i)
  have hsource(i:ι):((χ i).modulus.absNorm:ℝ)≤Cscale*Z^(0:ℝ)*Z^along:=by
    simp only [Real.rpow_zero,mul_one]
    exact (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hscale.le)
  have hh:=henergy G (fun _=>Z^along) P Src Z Rcap hSrc hZ.1.le hR
    (fun _=>Real.rpow_pos_of_pos hz _) hGS hcap hsource
  rw [show (xi/2)/2=xi/4 by ring] at hh
  simp only [hzero,zero_mul,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
    mul_zero,zero_add] at hh
  exact ⟨hzero,hh⟩

theorem radial_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ:O→Character)(P:O→ℂ)(omega:O→ℝ)
        (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Pbound:ℝ)(Wshort:ℝ→ℂ)
        (c d Z M along Xshort Src Rcap:ℝ),
      Z₀≤Z → 0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,‖P z‖≤Pbound) → (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → 0<Xshort →
      M+xi<along → 0<Src → 1≤Rcap →
      (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,Z₀,hC,hZ₀,hfinite⟩:=finite_original_error xi saving Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,Z₀,hC,hZ₀,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d Z M along Xshort Src Rcap
    hZ hK hΦ hP hχ hd hshort hXshort hfar hSrc hR hGS hmod hcap
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hshortsum:=single_radial_summable χ P omega Wshort c d Xshort Pbound hd hXshort
    hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  have hmem(z:↥S):keep (z:O):=(Finset.mem_filter.mp z.property).2
  obtain ⟨ψ,hψ,hf⟩:=hfinite (fun z:↥S=>χ z) (fun z=>hχ z (hmem z))
  let Q(z:↥S):ℂ:=
    (polynomial (χ z) false Wshort Xshort 0 (omega z)*P z)*
      (Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=(hf (fun z:↥S=>G z) Q Z M along Src Rcap hZ hfar hSrc hR
    (fun z=>hGS z (hmem z)) (fun z=>hmod z (hmem z)) (fun z=>hcap z (hmem z))).2
  simp only [Q,←mul_assoc] at hh
  rw [finite_weighted rows keep
      (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ,
    finite_weighted rows keep
      (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl))
    (by positivity))

theorem natural_polynomials_summable {Z Bmask bΦ:ℝ}(state:NaturalState Z Bmask bΦ)
    (Wlong Wshort:𝓢(ℝ,ℂ))(a b Xlong Xshort t omega:ℝ)
    (hb:0≤b)(hXlong:0<Xlong)(hXshort:0<Xshort)
    (hsLong:Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b)
    (hsShort:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b):
    Summable (fun z:O=>if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wlong Xlong 0 t*
        polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖eisEmbedding z‖^2/state.radial.scale)).re else 0) ∧
    Summable (fun z:O=>if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖eisEmbedding z‖^2/state.radial.scale)).re else 0):=by
  constructor
  · simpa only [mul_one] using pair_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=>t) (fun _=>omega) Wlong Wshort a b a b Xlong Xshort 1
      hb hb hXlong hXshort hsLong hsShort (fun _=>by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos
  · simpa only [mul_one] using single_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=>omega) Wshort a b Xshort 1 hb hXshort hsShort (fun _=>by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos

theorem natural_original_error (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        (effectiveState state).radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
          (effectiveState state).radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨H,C,Z₀,hC,hZ₀,hr⟩:=radial_original_error xi saving
    ((fixedConductorFactor:ℝ)*bΦ) epsilon hxi (mul_pos conductorFactor_pos hbΦ) hepsilon
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hz:1<Z:=hZ₀.trans_le hZ
  refine ⟨hz,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,summand,radialEnergy]
  have hpos:0<sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤ sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  have hh:=hr (fun _=>G) (naturalCharacter state.character) (fun _=>1) (fun _=>omega)
    (effectiveState state).radial.keep state.radial.profile state.radial.scale 1
    Wshort a b Z state.width along Xshort Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width)) hZ state.radial.scale_pos
    state.radial.nonneg (fun _=>by simp) (effective_character_nonprincipal state)
    hb hsShort hXshort hfar hSrc (le_max_left _ _) (fun _ _=>hnorm)
    (effective_character_cap state hbΦ.le)
    (fun z hz=>(effective_character_cap state hbΦ.le z hz).trans (le_max_right _ _))
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t,mul_one] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

theorem short_radial_mass (χ:O→Character)(W:𝓢(ℝ,ℂ))(a b X:ℝ)
    (hb:0≤b)(hX:0<X)(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (omega:O→ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K):
    radialEnergy (fun z=>polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (128*max 1 b)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
        QuadraticInitialBound.diagonalControl Φ*max 1 K*X:=by
  let A:=((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)
  let V:=(128*max 1 b*A)^2*X
  have hV:0≤V:=by dsimp [V];positivity
  have hp(z:O):‖polynomial (χ z) false W X 0 (omega z)‖^2≤V:=by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (CenteredMomentOriginalReflectionErrorMass.plain_polynomial_bound (χ z) W b A X (omega z)
        (apply_nonneg _ _) hX (SchwartzMap.norm_le_seminorm ℝ W) (fun y hy=>(hs hy).2)) 2
    simpa only [mul_pow,Real.sq_sqrt hX.le,V] using hh
  have hsum:=single_radial_summable χ (fun _=>1) omega W a b X 1 hb hX hs
    (fun _=>by simp) keep Φ K hK
  simp only [mul_one] at hsum
  have hweight:=CenteredMomentAbsoluteEnergy.radial_norm_summable Φ K hK
  have hh:radialEnergy (fun z=>polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=by
    rw [←tsum_mul_right]
    apply hsum.tsum_le_tsum _ (hweight.mul_right V)
    intro z
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _)).trans_eq (mul_comm _ _))
    · exact mul_nonneg (norm_nonneg _) hV
  apply (hh.trans (mul_le_mul_of_nonneg_right
    (CenteredMomentAbsoluteEnergy.radial_weight_lattice_bound_all Φ K hK) hV)).trans_eq
  dsimp [V,A]
  ring

theorem natural_original_error_mass (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        state.radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        QuadraticInitialBound.diagonalControl state.radial.profile*max 1 state.radial.scale*Xshort:=by
  obtain ⟨n,S,C,hC,h⟩:=natural_original_error a b bΦ epsilon xi saving ha hb hbΦ hepsilon hxi
  refine ⟨n,S,C*(128*max 1 b)^2,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have hh:=hZ.2 Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have he(f:O→ℂ):radialEnergy f (effectiveState state).radial.keep
      state.radial.profile state.radial.scale=
      radialEnergy f state.radial.keep state.radial.profile state.radial.scale:=
    radialEnergy_effective state.radial f
  rw [he,he] at hh
  have hm:=short_radial_mass (naturalCharacter state.character) Wshort a b Xshort
    hb hXshort hsShort (fun _=>omega) state.radial.keep state.radial.profile
    state.radial.scale state.radial.scale_pos
  have hz:0<Z:=zero_lt_one.trans hZ.1
  apply (hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))).trans_eq
  ring

end SevenEighths.CenteredMomentEnergyZeroRetainedError

end

end OAI

end

