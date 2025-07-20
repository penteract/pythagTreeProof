import Mathlib
import Proof.Eqns
import Proof.CertProof
import Proof.TileAreaOpt
import Proof.Lemmas.List

theorem volFin {ps : List Piece} : vol ps ≠ ⊤ := by
  apply (ne_top_of_lt (b:=⊤))
  simp only [vol, Function.comp_apply]
  apply LE.le.trans_lt (MeasureTheory.measure_mono getTiles_in_usq)
  rw [vol_usq]
  exact ENNReal.one_lt_top


theorem vol_cors (ps : List Piece) : vol ps =
    vol (canon_cor_rot Cor.tl ps) / 4 +
    vol (canon_cor_rot Cor.br ps) / 4 +
    vol (canon_cor_rot Cor.bl ps) / 4 +
    vol (canon_cor_rot Cor.tr ps) / 4 := by
    rw [vol,Function.comp_apply]
    nth_rw 1 [vol_corners_sorted]
    simp only [Function.comp_apply]
    ring -- rearrange things due to the version I used to generate allparts

theorem vol_cors' (ps : List Piece) : vol' ps =
    vol' (canon_cor_rot Cor.tl ps) / 4 +
    vol' (canon_cor_rot Cor.br ps) / 4 +
    vol' (canon_cor_rot Cor.bl ps) / 4 +
    vol' (canon_cor_rot Cor.tr ps) / 4 := by
  have h:= @volFin ps
  simp_all only [vol_cors ps, vol']
  -- #check ENNReal.add_ne_top.mp h
  have ⟨h4',h4⟩ := (ENNReal.add_ne_top.mp h)
  have ⟨h3',h3⟩ := ENNReal.add_ne_top.mp h4'
  have ⟨ h1,h2⟩:= ENNReal.add_ne_top.mp h3'
  rw [← ENNReal.toReal_ofNat 4]
  simp only [← ENNReal.toReal_div]
  let tst := ENNReal.toReal_add h1 h2
  rw [← ENNReal.toReal_add h1 h2,
      ← ENNReal.toReal_add h3' h3,
      ← ENNReal.toReal_add h4' h4]

theorem vol_full' : vol' [Piece.fullPiece] = 1 := by
  simp [getTiles,getTile,vol_usq,vol,vol']

theorem vol_empty' : vol' [] = 0 := by
  simp [getTiles,getTile,vol,vol']


-- set_option maxRecDepth 200
theorem evalWith_vol'_is_system -- (h : x ∈ pyt_eqns)
    : ∀ x∈ pyt_eqns, Eqns.evalWith vol' x.1 = (0:ℝ) := by
  intro x h
  unfold pyt_eqns at h
  simp only [List.mem_map, Prod.exists] at h
  obtain ⟨a,b,q,⟨abqinap, h⟩ ⟩ := h
  have ap :=allParts_describes_pyt _ abqinap
  simp at ap
  simp only [Eqns.fromAllParts,ap] at h
  rw [← h]
  unfold Eqns.evalWith
  rw [List.map_cons,List.sum_cons]
  rw [vol_cors']
  simp only [Rat.cast_ofNat, List.map_cons, List.map_nil, Rat.cast_neg, Rat.cast_one, neg_mul,
    one_mul, List.sum_cons, List.sum_nil, add_zero]
  ring

theorem evalVol_inits_sub : Eqns.evalWith vol' (init.map (fun x => (x,(1:ℚ))) ++ [([],-Eqns.qEmpty),([Piece.fullPiece],-Eqns.qFull) ]) = 0 := by
  rw [← Eqns.permEq (apeq)]
  unfold pyt_sum
  rw [Eqns.eval_toCoeffs_merged]
  exact evalWith_vol'_is_system

theorem vol_inits_val' : List.sum (List.map vol' init) = Eqns.qFull * vol' [Piece.fullPiece] + Eqns.qEmpty * vol' [] := by
  linear_combination (norm:=ring_nf) evalVol_inits_sub
  rw [Eqns.appendEq]
  unfold Eqns.evalWith
  simp only [List.map_map, List.map_cons, Rat.cast_neg, neg_mul, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  ring_nf
  conv_lhs =>
    enter[2,1,1,x]
    simp
  ring

theorem vol_inits_val : List.sum (List.map vol' init) = Eqns.qFull := by
  rw [vol_inits_val']
  rw [vol_full',vol_empty']
  ring_nf
