module
public import Swanepoel.HalfSystemBankRealization
public import Swanepoel.JoinClosedCrossings
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem TrackSystem.internal_image_of_injOn (D E : TrackSystem)
    (A : Finset D.Track) (f : D.Track→E.Track) (hf : Set.InjOn f (A : Set D.Track))
    (hAdj : ∀ u∈A,∀ v∈A,E.crossing.Adj (f u) (f v) ↔ D.crossing.Adj u v) :
    E.internal (A.image f)=D.internal A := by
  induction A using Finset.induction_on with
  | empty => simp [TrackSystem.internal_sum]
  | @insert u A hu ih =>
    have hsub : A⊆insert u A := Finset.subset_insert _ _
    have hfu : f u∉A.image f := by
      intro hm
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hm
      exact hu ((hf (hsub hv) (Finset.mem_insert_self _ _) hvu) ▸ hv)
    have hfilter : (A.image f).filter (E.crossing.Adj (f u))=
        (A.filter (D.crossing.Adj u)).image f := by
      ext w
      constructor
      · intro hw
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).1
        exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,
          (hAdj u (Finset.mem_insert_self _ _) v (hsub hv)).mp (Finset.mem_filter.mp hw).2⟩,rfl⟩
      · intro hw
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,rfl⟩,
          (hAdj u (Finset.mem_insert_self _ _) v (hsub (Finset.mem_filter.mp hv).1)).mpr
            (Finset.mem_filter.mp hv).2⟩
    rw [Finset.image_insert,E.internal_insert _ _ hfu,D.internal_insert _ _ hu,
      ih (hf.mono hsub) (fun a ha b hb => hAdj a (hsub ha) b (hsub hb)),hfilter,
      Finset.card_image_of_injOn (hf.mono ((Finset.filter_subset _ _).trans hsub))]

def HalfSystem.BankRealization.TerminalCrossing {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side) : Prop :=
  ∀ u∈H.tracks.terminal,∀ v∈H.tracks.terminal,
    H.tracks.crossing.Adj u v ↔ ComponentCrosses (R.component u) (R.component v)

theorem HalfSystem.BankRealization.R_eq_actual_bank {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side)
    (hcross : R.TerminalCrossing) :
    H.R=(G.familyInternalCrossings ht (B.bankDefectFamily ht side) : ℤ)+
      (B.bankDefectFamily ht side).card := by
  let D := componentSystem G ht ∅ 0
  let f : H.tracks.Track→D.Track := fun u => Fintype.equivFin (TrackComponent G) (R.component u)
  have hf : Function.Injective f := (Fintype.equivFin (TrackComponent G)).injective.comp R.injective
  have hAdj : ∀ u∈H.tracks.terminal,∀ v∈H.tracks.terminal,
      D.crossing.Adj (f u) (f v) ↔ H.tracks.crossing.Adj u v := by
    intro u hu v hv
    change ComponentCrosses ((Fintype.equivFin (TrackComponent G)).symm (f u))
      ((Fintype.equivFin (TrackComponent G)).symm (f v)) ↔ _
    simpa only [f,Equiv.symm_apply_apply] using (hcross u hu v hv).symm
  have himage : H.tracks.terminal.image f=G.familyTrackIndices (B.bankDefectFamily ht side) := by
    unfold PennyGraph.familyTrackIndices
    rw [Finset.map_eq_image]
    change H.tracks.terminal.image (fun u => Fintype.equivFin (TrackComponent G) (R.component u))=
      (B.bankAnchorTracks ht side).image (Fintype.equivFin (TrackComponent G))
    rw [← R.anchors,Finset.image_image]
    rfl
  have hcount := H.tracks.internal_image_of_injOn D H.tracks.terminal f hf.injOn hAdj
  rw [himage] at hcount
  change (H.tracks.internal H.tracks.terminal : ℤ)+H.tracks.defects=_
  rw [← hcount,R.defects]
  rfl

end Swanepoel
