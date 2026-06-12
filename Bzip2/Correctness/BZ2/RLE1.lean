import Bzip2.Format.BZ2.Transform
import Bzip2.Format.BZ2.Decoder

/-!
# Initial RLE1 transform roundtrip

Proves `decodeInitialRLE (encodeInitialRLE x) = x`: the outer bzip2 run-length
transform is invertible. The argument factors through a clean run-decomposition
spec `runTokens`, shows the runtime tail-recursive `rle1Tokens` equals it,
establishes that the encoded chunk stream is well-formed, and proves the decoder
inverts any well-formed chunk stream.
-/

namespace Bzip2.Format.BZ2

set_option autoImplicit false

/-- Expansion of a token list back to raw bytes: each `(byte, len)` is `len` copies. -/
def expand (tokens : List (UInt8 × Nat)) : List UInt8 :=
  tokens.flatMap (fun t => List.replicate t.2 t.1)

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_cons (t : UInt8 × Nat) (ts : List (UInt8 × Nat)) :
    expand (t :: ts) = List.replicate t.2 t.1 ++ expand ts := by
  simp [expand]

theorem expand_append (ts us : List (UInt8 × Nat)) :
    expand (ts ++ us) = expand ts ++ expand us := by
  simp [expand, List.flatMap_append]

/-- Clean run-decomposition spec: complete the in-progress run `(cur, cnt)`, then
continue over `rest`. The runtime `rle1Tokens` is proved equal to this below. -/
def runTokens (cur : UInt8) (cnt : Nat) : List UInt8 → List (UInt8 × Nat)
  | [] => runChunks cur cnt
  | x :: xs =>
      if x = cur then runTokens cur (cnt + 1) xs
      else runChunks cur cnt ++ runTokens x 1 xs
termination_by rest => rest.length

/-- `pushRunChunksRev` is the reverse of the forward `runChunks`, prepended to `acc`. -/
theorem pushRunChunksRev_eq (b : UInt8) (n : Nat) (acc : List (UInt8 × Nat)) :
    pushRunChunksRev b n acc = (runChunks b n).reverse ++ acc := by
  induction n using Nat.strong_induction_on generalizing acc with
  | _ n ih =>
      match n with
      | 0 => simp [pushRunChunksRev, runChunks]
      | m + 1 =>
          rw [pushRunChunksRev, runChunks]
          have hlt : m + 1 - min (m + 1) 255 < m + 1 := by omega
          rw [ih _ hlt]
          simp [List.reverse_append]

/-- Expanding the forward run chunks gives `n` copies of the byte. -/
theorem expand_runChunks (b : UInt8) (n : Nat) :
    expand (runChunks b n) = List.replicate n b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [runChunks]
      | m + 1 =>
          rw [runChunks]
          have hlt : m + 1 - min (m + 1) 255 < m + 1 := by omega
          rw [expand_cons, ih _ hlt, ← List.replicate_add]
          congr 1
          omega

/-- The tail-recursive worker, reversed, equals `acc` reversed followed by `runTokens`. -/
theorem rle1TokensRev_reverse (cur : UInt8) (cnt : Nat) (rest : List UInt8)
    (acc : List (UInt8 × Nat)) :
    (rle1TokensRev cur cnt rest acc).reverse = acc.reverse ++ runTokens cur cnt rest := by
  induction rest generalizing cur cnt acc with
  | nil =>
      rw [rle1TokensRev, runTokens, pushRunChunksRev_eq]
      simp
  | cons x xs ih =>
      rw [rle1TokensRev, runTokens]
      by_cases hx : x = cur
      · simp only [hx, if_pos]
        rw [ih cur (cnt + 1) acc]
      · simp only [hx, if_false]
        rw [ih x 1 (pushRunChunksRev cur cnt acc), pushRunChunksRev_eq]
        simp [List.append_assoc]

theorem rle1Tokens_eq (xs : List UInt8) :
    rle1Tokens xs = match xs with
      | [] => []
      | b :: rest => runTokens b 1 rest := by
  match xs with
  | [] => rfl
  | b :: rest =>
      show (rle1TokensRev b 1 rest []).reverse = runTokens b 1 rest
      rw [rle1TokensRev_reverse]
      simp

/-- Expanding the run-tokens recovers the in-progress run prepended to the rest. -/
theorem expand_runTokens (cur : UInt8) (cnt : Nat) (rest : List UInt8) :
    expand (runTokens cur cnt rest) = List.replicate cnt cur ++ rest := by
  induction rest generalizing cur cnt with
  | nil => rw [runTokens, expand_runChunks]; simp
  | cons x xs ih =>
      rw [runTokens]
      by_cases hx : x = cur
      · simp only [hx, if_pos]
        rw [ih cur (cnt + 1), List.replicate_add]
        simp
      · simp only [hx, if_false]
        rw [expand_append, expand_runChunks, ih x 1]
        simp

/-- **The tokenizer faithfully decomposes the input.** -/
theorem expand_rle1Tokens (xs : List UInt8) : expand (rle1Tokens xs) = xs := by
  rw [rle1Tokens_eq]
  match xs with
  | [] => simp
  | b :: rest =>
      simp only
      rw [expand_runTokens]
      simp

/-! ### ByteArray ↔ List bridges -/

private theorem toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction i, r using ByteArray.toList.loop.induct (bs := bs) with
  | case1 i r hlt ih =>
      rw [ByteArray.toList.loop, if_pos hlt, ih]
      have hi : i < bs.data.toList.length := by simpa using hlt
      have hget : bs.get! i = bs.data.toList[i] := by
        simp only [ByteArray.get!, Array.getElem_toList]
        exact getElem!_pos bs.data i (by simpa using hlt)
      rw [List.drop_eq_getElem_cons hi, hget]
      simp
  | case2 i r hge =>
      rw [ByteArray.toList.loop, if_neg hge]
      have : bs.data.toList.length ≤ i := by simpa using hge
      simp [List.drop_eq_nil_of_le this]

theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop_eq]; simp

theorem toList_push (out : ByteArray) (b : UInt8) :
    (out.push b).toList = out.toList ++ [b] := by
  rw [toList_eq, toList_eq, ByteArray.data_push, Array.toList_push]

theorem toList_pushCopies (out : ByteArray) (b : UInt8) (n : Nat) :
    (pushCopies out b n).toList = out.toList ++ List.replicate n b := by
  induction n generalizing out with
  | zero => simp [pushCopies]
  | succ m ih =>
      rw [pushCopies, ih, toList_push, List.replicate_succ]
      simp

/-! ### Decoder inverts well-formed chunk streams -/

/-- The chunk bytes of one token, as a list. -/
def chunkStream (tokens : List (UInt8 × Nat)) : List UInt8 :=
  tokens.flatMap (fun t => rle1ChunkBytes t.1 t.2)

@[simp] theorem chunkStream_nil : chunkStream [] = [] := rfl

theorem chunkStream_cons (t : UInt8 × Nat) (ts : List (UInt8 × Nat)) :
    chunkStream (t :: ts) = rle1ChunkBytes t.1 t.2 ++ chunkStream ts := by
  simp [chunkStream]

/--
A single literal byte at the head decodes to one pushed byte, provided it does
not begin a run of four equal bytes (i.e. the next three are not all `b`).
-/
theorem decode_lit_step (b : UInt8) (zs : List UInt8) (out : ByteArray)
    (h : zs.take 3 ≠ List.replicate 3 b) :
    decodeInitialRLEAux (b :: zs) out = decodeInitialRLEAux zs (out.push b) := by
  match zs with
  | b₂ :: b₃ :: b₄ :: cnt :: rest =>
      conv_lhs => rw [decodeInitialRLEAux]
      have hg : ¬ ((b = b₂ ∧ b₂ = b₃) ∧ b₃ = b₄) := by
        rintro ⟨⟨rfl, rfl⟩, rfl⟩
        exact h rfl
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, if_neg hg]
  | [] => simp [decodeInitialRLEAux]
  | [b₂] => simp [decodeInitialRLEAux]
  | [b₂, b₃] => simp [decodeInitialRLEAux]
  | [b₂, b₃, b₄] => simp [decodeInitialRLEAux]

/-- Decoding a literal run of `k ≤ 3` copies of `b` followed by bytes not
beginning with `b` emits exactly `k` copies and continues. -/
theorem decodeLitRun (k : Nat) (hk : k ≤ 3) (b : UInt8) (ys : List UInt8) (out : ByteArray)
    (hys : ys.head? ≠ some b) :
    decodeInitialRLEAux (List.replicate k b ++ ys) out
      = decodeInitialRLEAux ys (pushCopies out b k) := by
  induction k generalizing out with
  | zero => simp [pushCopies]
  | succ m ih =>
      rw [List.replicate_succ, List.cons_append]
      rw [decode_lit_step b (List.replicate m b ++ ys) out (by
        -- the first three bytes after the head are at most `m ≤ 2` copies of `b`
        -- then `ys`, whose head ≠ b, so they are not all `b`
        intro hcontra
        have hm : m ≤ 2 := by omega
        match ys, hys with
        | [], _ =>
            have := congrArg List.length hcontra
            simp [List.take, List.replicate] at this
            omega
        | y :: ys', hys' =>
            have hy : y ≠ b := by simpa using hys'
            interval_cases m <;>
              simp_all [List.take, List.replicate])]
      rw [pushCopies]
      exact ih (by omega) (out.push b)

theorem pushCopies_add (out : ByteArray) (b : UInt8) (m n : Nat) :
    pushCopies out b (m + n) = pushCopies (pushCopies out b m) b n := by
  induction m generalizing out with
  | zero => simp [pushCopies]
  | succ k ih => rw [Nat.succ_add, pushCopies, pushCopies, ih]

/-- A chunk of `len ≥ 4` copies decodes (via the 4-equal-bytes-plus-count rule)
to exactly `len` pushed copies and continues. -/
theorem decode_run4_step (b : UInt8) (len : Nat) (ys : List UInt8) (out : ByteArray)
    (h4 : 4 ≤ len) (h255 : len ≤ 255) :
    decodeInitialRLEAux (rle1ChunkBytes b len ++ ys) out
      = decodeInitialRLEAux ys (pushCopies out b len) := by
  have hchunk : rle1ChunkBytes b len = b :: b :: b :: b :: [UInt8.ofNat (len - 4)] := by
    unfold rle1ChunkBytes
    rw [if_neg (by omega)]
    simp [List.replicate]
  rw [hchunk]
  simp only [List.cons_append, List.nil_append]
  conv_lhs => rw [decodeInitialRLEAux]
  rw [if_pos (by simp)]
  have hcnt : (UInt8.ofNat (len - 4)).toNat = len - 4 := by
    have hsz : len - 4 < UInt8.size := by have : UInt8.size = 256 := rfl; omega
    exact UInt8.toNat_ofNat_of_lt' hsz
  have hsum : (4 : Nat) + (len - 4) = len := Nat.add_sub_cancel' h4
  simp only [hcnt,
    show ((((out.push b).push b).push b).push b) = pushCopies out b 4 from by simp [pushCopies],
    ← pushCopies_add, hsum]

/-! ### Well-formedness of RLE1 chunk streams -/

/-- A chunk stream token list is well formed when every length is in `[1, 255]`
and each literal (`≤ 3`) token is followed by a token of a different byte. -/
def Rle1WF : List (UInt8 × Nat) → Prop
  | [] => True
  | t :: rest =>
      1 ≤ t.2 ∧ t.2 ≤ 255 ∧ (t.2 ≤ 3 → (rest.head?.map Prod.fst) ≠ some t.1) ∧ Rle1WF rest

theorem rle1ChunkBytes_head? (b : UInt8) (len : Nat) (h : 1 ≤ len) :
    (rle1ChunkBytes b len).head? = some b := by
  unfold rle1ChunkBytes
  split
  · cases len with
    | zero => omega
    | succ k => simp [List.replicate]
  · simp [List.replicate]

theorem chunkStream_head? (t : UInt8 × Nat) (rest : List (UInt8 × Nat)) (h : 1 ≤ t.2) :
    (chunkStream (t :: rest)).head? = some t.1 := by
  rw [chunkStream_cons, List.head?_append, rle1ChunkBytes_head? t.1 t.2 h]
  rfl

/-- **Decoder inverts a well-formed chunk stream.** -/
theorem decode_chunkStream (tokens : List (UInt8 × Nat)) (out : ByteArray)
    (hwf : Rle1WF tokens) :
    (decodeInitialRLEAux (chunkStream tokens) out).toList = out.toList ++ expand tokens := by
  induction tokens generalizing out with
  | nil => simp [chunkStream, decodeInitialRLEAux]
  | cons t rest ih =>
      obtain ⟨hlo, hhi, hlit, hwfrest⟩ := hwf
      rw [chunkStream_cons]
      by_cases h4 : 4 ≤ t.2
      · rw [decode_run4_step t.1 t.2 (chunkStream rest) out h4 hhi, ih _ hwfrest,
          toList_pushCopies]
        simp [expand_cons, List.append_assoc]
      · -- literal chunk: t.2 ≤ 3
        have hle3 : t.2 ≤ 3 := by omega
        have hbytes : rle1ChunkBytes t.1 t.2 = List.replicate t.2 t.1 := by
          unfold rle1ChunkBytes; rw [if_pos hle3]
        have hhead : (chunkStream rest).head? ≠ some t.1 := by
          cases rest with
          | nil => simp [chunkStream]
          | cons u rest' =>
              rw [chunkStream_head? u rest' (by
                have := hwfrest; cases this; assumption)]
              have := hlit hle3
              simpa using this
        rw [hbytes, decodeLitRun t.2 hle3 t.1 (chunkStream rest) out hhead,
          ih _ hwfrest, toList_pushCopies]
        simp [expand_cons, List.append_assoc]

/-! ### The tokenizer produces well-formed streams -/

theorem Rle1WF_runChunks_append (b : UInt8) (n : Nat) (more : List (UInt8 × Nat))
    (hn : 1 ≤ n) (hmore : Rle1WF more) (hhead : more.head?.map Prod.fst ≠ some b) :
    Rle1WF (runChunks b n ++ more) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n, hn with
      | m + 1, _ =>
          rw [runChunks]
          by_cases hsmall : m + 1 ≤ 255
          · have : min (m + 1) 255 = m + 1 := by omega
            rw [this]
            have : m + 1 - (m + 1) = 0 := by omega
            rw [this, runChunks]
            refine ⟨by omega, by omega, ?_, hmore⟩
            intro _
            exact hhead
          · have hmin : min (m + 1) 255 = 255 := by omega
            rw [hmin]
            have hrec : 1 ≤ m + 1 - 255 := by omega
            refine ⟨by omega, by omega, ?_, ?_⟩
            · intro hc; omega
            · exact ih (m + 1 - 255) (by omega) hrec

theorem runChunks_head?_fst (b : UInt8) (n : Nat) (hn : 1 ≤ n) :
    (runChunks b n).head?.map Prod.fst = some b := by
  match n, hn with
  | m + 1, _ => rw [runChunks]; simp

theorem runTokens_head?_fst (cur : UInt8) (cnt : Nat) (rest : List UInt8) (hcnt : 1 ≤ cnt) :
    (runTokens cur cnt rest).head?.map Prod.fst = some cur := by
  induction rest generalizing cur cnt with
  | nil => rw [runTokens]; exact runChunks_head?_fst cur cnt hcnt
  | cons x xs ih =>
      rw [runTokens]
      by_cases hx : x = cur
      · simp only [hx, if_pos]
        exact ih cur (cnt + 1) (by omega)
      · simp only [hx, if_false]
        match cnt, hcnt with
        | k + 1, _ =>
            rw [runChunks]
            simp

theorem Rle1WF_runTokens (cur : UInt8) (cnt : Nat) (rest : List UInt8) (hcnt : 1 ≤ cnt) :
    Rle1WF (runTokens cur cnt rest) := by
  induction rest generalizing cur cnt with
  | nil =>
      rw [runTokens, show runChunks cur cnt = runChunks cur cnt ++ [] from by simp]
      exact Rle1WF_runChunks_append cur cnt [] hcnt trivial (by simp)
  | cons x xs ih =>
      rw [runTokens]
      by_cases hx : x = cur
      · simp only [hx, if_pos]
        exact ih cur (cnt + 1) (by omega)
      · simp only [hx, if_false]
        refine Rle1WF_runChunks_append cur cnt (runTokens x 1 xs) hcnt (ih x 1 (by omega)) ?_
        rw [runTokens_head?_fst x 1 xs (by omega)]
        simpa using hx

/-- Well-formedness of the chunk stream produced by the tokenizer. -/
theorem Rle1WF_rle1Tokens (xs : List UInt8) : Rle1WF (rle1Tokens xs) := by
  rw [rle1Tokens_eq]
  match xs with
  | [] => trivial
  | b :: rest => exact Rle1WF_runTokens b 1 rest (by omega)

/-! ### Assembling the RLE1 round trip -/

/-- Folding `ByteArray.push` over a list appends that list to the byte array's contents. -/
theorem toList_foldl_push (out : ByteArray) (l : List UInt8) :
    (l.foldl ByteArray.push out).toList = out.toList ++ l := by
  induction l generalizing out with
  | nil => simp
  | cons b bs ih => rw [List.foldl_cons, ih, toList_push]; simp

/-- One token's wire bytes append its chunk bytes. -/
theorem toList_appendTokenBytes (out : ByteArray) (t : UInt8 × Nat) :
    (appendTokenBytes out t).toList = out.toList ++ rle1ChunkBytes t.1 t.2 := by
  rw [appendTokenBytes, toList_foldl_push]

/-- Folding the encoder over a token list yields exactly the chunk stream. -/
theorem toList_foldl_appendTokenBytes (out : ByteArray) (tokens : List (UInt8 × Nat)) :
    (tokens.foldl appendTokenBytes out).toList = out.toList ++ chunkStream tokens := by
  induction tokens generalizing out with
  | nil => simp [chunkStream]
  | cons t ts ih =>
      rw [List.foldl_cons, ih, toList_appendTokenBytes, chunkStream_cons]
      simp [List.append_assoc]

/-- The encoder's output, as a list, is the chunk stream of the run-tokens. -/
theorem toList_encodeInitialRLE (x : ByteArray) :
    (encodeInitialRLE x).toList = chunkStream (rle1Tokens x.toList) := by
  rw [encodeInitialRLE, toList_foldl_appendTokenBytes]
  simp

/-- **The bzip2 initial RLE1 transform round-trips.**
`decodeInitialRLE` recovers the original bytes from `encodeInitialRLE`. -/
theorem decodeInitialRLE_encodeInitialRLE (x : ByteArray) :
    (decodeInitialRLE (encodeInitialRLE x)).toList = x.toList := by
  rw [decodeInitialRLE, toList_encodeInitialRLE,
    decode_chunkStream _ ByteArray.empty (Rle1WF_rle1Tokens x.toList),
    expand_rle1Tokens]
  simp [toList_eq]

end Bzip2.Format.BZ2
