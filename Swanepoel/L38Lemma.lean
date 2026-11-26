module
public import Swanepoel.L38WeightedBankEstimate
public import Swanepoel.L38HalfPentagonEstimates
public import Swanepoel.L38BankCountAssembly
public import Swanepoel.L38HalfReduction
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem lemma_3_8 (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hhigh : 39*B.bankK ht side≤100*((B.bankMeetingAnchors ht side).card : ℤ)) :
    G.familyR ht (B.bankDefectFamily ht side)≤
      ((B.bankMeetingAnchors ht side).card : ℤ)*
        (B.bankK ht side-(B.bankMeetingAnchors ht side).card) := by
  let S := B.isolatedTwoPortPentagons ht side
  let Y := B.bankRemainder ht side
  let ell : ℝ := S.card
  let k : ℝ := G.familyK Y
  let y : ℝ := (B.subfamilyMeetingPorts Y).card
  let h : ℝ := G.familyPortExcess Y
  let X : ℝ := (G.familyInternalCrossings ht S : ℝ)+S.card
  let M : ℝ := G.interFamilyCrossings ht S Y
  let Z : ℝ := (G.familyInternalCrossings ht Y : ℝ)+Y.card
  let r : ℝ := G.familyR ht (B.bankDefectFamily ht side)
  obtain ⟨hell,hk,hy,hh,hK,hD,hthree,hfour,hfive⟩ := B.bank_arithmetic_parameters ht side hdegree
  change (B.bankK ht side : ℝ)=3*ell+k at hK
  change ((B.bankMeetingAnchors ht side).card : ℝ)=2*ell+y at hD
  have hX : X≤3*ell^2/2 := B.bank_isolated_X_bound ht hc hdegree hcut side
  have hM : M≤ell*(k+h) := by
    have hm := B.bank_isolated_M_bound ht hc hdegree hcut side
    dsimp only [M,ell,k,h,S,Y]
    exact_mod_cast hm
  have hR : r=X+M+Z := by
    dsimp only [r,X,M,Z]
    exact_mod_cast B.bank_weighted_count_split ht side
  have harea : X/4+M/2+Z≤(411/2500:ℝ)*(5*ell/2+2*k-h-2*(ell+y)/3)^2 := by
    convert B.bank_weighted_area_estimate ht hc hdegree hcut side using 1;
      dsimp only [X,M,Z,ell,k,h,y,S,Y]; ring
  have hraw := bankRawU_of_weighted_counts ell k y h r X M Z
    (5*ell/2+2*k-h) (ell+y) hR hX hM rfl rfl harea
  have hQ := B.bank_family_quadratic ht hc hdegree hcut side
  have hbankK : G.familyK (B.bankDefectFamily ht side)=B.bankK ht side := rfl
  rw [hbankK] at hQ
  have hQr : (10000:ℝ)*r≤2379*(B.bankK ht side : ℝ)^2 := by
    dsimp only [r]
    exact_mod_cast hQ
  rw [hK] at hQr
  have hquad : r≤(2379/10000:ℝ)*(3*ell+k)^2 := by linarith only [hQr]
  have hhi : (39:ℝ)*(B.bankK ht side : ℝ)≤100*((B.bankMeetingAnchors ht side).card : ℝ) := by
    exact_mod_cast hhigh
  rw [hK,hD] at hhi
  have hlo : (39/100:ℝ)*(3*ell+k)≤2*ell+y := by linarith only [hhi]
  have hb := lemma_3_8_of_geometric_estimates ell k y h r hell hk hy hh hthree hfour hfive hquad hraw hlo
  rw [← hK,← hD] at hb
  dsimp only [r] at hb
  exact_mod_cast hb

end OrdinaryCutBanks

theorem HalfSystem.BankRealization.highBankBound_of_terminalCrossing
    {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} {H : HalfSystem}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (R : H.BankRealization B ht side) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (hcross : R.TerminalCrossing) : H.HighBankBound := by
  intro hhigh
  have hK := R.k_eq_bankK
  have hD := R.d_eq_bankMeetingAnchors
  rw [hK,hD] at hhigh
  have hb := B.lemma_3_8 ht hc hdegree hcut side hhigh
  change H.R≤H.d*(H.k-H.d)
  rw [R.R_eq_actual_bank hcross,hK,hD]
  exact hb

theorem HalfSystem.BankRealization.highBankBound
    {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} {H : HalfSystem}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (R : H.BankRealization B ht side) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) : H.HighBankBound :=
  R.highBankBound_of_terminalCrossing hc hdegree hcut R.terminal_crossing

theorem OrdinaryCutBanks.canonicalHalfSystem_lemma_3_8
    {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalHalfSystem ht side).HighBankBound :=
  (B.canonicalHalfBankRealization ht hc hcut side).highBankBound_of_terminalCrossing hc hdegree hcut
    (B.canonicalHalfBankRealization_terminalCrossing ht hc hcut side)

end Swanepoel
