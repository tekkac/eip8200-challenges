import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# States and paths of the scalar-SWAR patterned-1000 guard

The guard carries the expected word forward instead of storing thirty-two of
them, so the scan is one loop: `wordPath` derives the word and routes the four
straddling offsets to `straddlePath`, and `comparePath` folds the difference
into the accumulator and advances the offset and the scalar.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/-- Push the five constants and start the scan. -/
def setupPath : List Located :=
  [opAt 2903 .JUMPDEST,
   pushAt 2904 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 2905 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 2906 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 2907 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 2908 (.Dup ⟨2, by decide⟩), opAt 2909 (.Dup ⟨2, by decide⟩),
   opAt 2910 .AND, pushAt 2911 0 0, pushAt 2912 0 0, pushAt 2913 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 2914 .JUMPDEST, opAt 2915 (.Dup ⟨0, by decide⟩),
   opAt 2916 (.Dup ⟨5, by decide⟩), opAt 2917 .MUL,
   opAt 2918 (.Dup ⟨0, by decide⟩), opAt 2919 (.Dup ⟨7, by decide⟩),
   opAt 2920 .AND, opAt 2921 (.Dup ⟨5, by decide⟩), opAt 2922 .ADD,
   opAt 2923 (.Dup ⟨1, by decide⟩), opAt 2924 (.Dup ⟨9, by decide⟩),
   opAt 2925 .XOR, opAt 2926 (.Dup ⟨10, by decide⟩), opAt 2927 .AND,
   opAt 2928 .XOR, opAt 2929 (.Dup ⟨3, by decide⟩), pushAt 2930 1 0xff,
   opAt 2931 .AND, pushAt 2932 1 0xe0, opAt 2933 .EQ, pushAt 2934 2 0x1490,
   opAt 2935 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 2936 .JUMPDEST, opAt 2937 (.Dup ⟨3, by decide⟩),
   opAt 2938 .CALLDATALOAD, opAt 2939 .XOR, opAt 2940 (.Dup ⟨4, by decide⟩),
   opAt 2941 .OR, opAt 2942 (.Swap ⟨3, by decide⟩), opAt 2943 .POP,
   opAt 2944 .POP, opAt 2945 .JUMPDEST, pushAt 2946 1 0xa0,
   opAt 2947 .ADD, pushAt 2948 1 0xff, opAt 2949 .AND,
   opAt 2950 .JUMPDEST, opAt 2951 .JUMPDEST,
   opAt 2952 (.Swap ⟨0, by decide⟩), pushAt 2953 1 0x20, opAt 2954 .ADD,
   opAt 2955 (.Swap ⟨0, by decide⟩), opAt 2956 .JUMPDEST,
   opAt 2957 (.Dup ⟨1, by decide⟩), pushAt 2958 2 0x03e0, opAt 2959 .GT,
   pushAt 2960 2 0x1418, opAt 2961 .JUMPI]

/-- The padded tail word and the branch to the out-of-line miss cleanup. -/
def tailPath : List Located :=
  [pushAt 2962 2 0x03e0, opAt 2963 .CALLDATALOAD,
   pushAt 2964 8 0x88add2f71c41668b, pushAt 2965 1 0xc0, opAt 2966 .SHL,
   opAt 2967 .XOR, opAt 2968 (.Dup ⟨3, by decide⟩), opAt 2969 .OR,
   pushAt 2970 2 0x1347, opAt 2971 .JUMPI]

/-- A miss lands in former guard filler, clears the retained scanner frame,
and rejoins the generic implementation with its original empty stack. -/
def cleanupPath : List Located :=
  [opAt 2864 .JUMPDEST,
   opAt 2865 .POP, opAt 2866 .POP, opAt 2867 .POP, opAt 2868 .POP,
   opAt 2869 .POP, opAt 2870 .POP, opAt 2871 .POP, opAt 2872 .POP,
   pushAt 2873 2 0x03ee, opAt 2874 .JUMP]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 2972 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 2973 0 0, opAt 2974 .MSTORE, pushAt 2975 1 0x20, pushAt 2976 0 0,
   opAt 2977 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 2989 .JUMPDEST, opAt 2990 (.Dup ⟨6, by decide⟩),
   opAt 2991 (.Dup ⟨4, by decide⟩), pushAt 2992 1 0x08, opAt 2993 .SHR,
   pushAt 2994 1 0x05, opAt 2995 .MUL, pushAt 2996 1 0x1b, opAt 2997 .SUB,
   pushAt 2998 1 0x08, opAt 2999 .MUL, opAt 3000 .SHR, pushAt 3001 1 0x0b,
   opAt 3002 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3003 (.Dup ⟨1, by decide⟩), opAt 3004 (.Dup ⟨9, by decide⟩),
   opAt 3005 .AND, opAt 3006 (.Dup ⟨1, by decide⟩), opAt 3007 .ADD,
   opAt 3008 (.Dup ⟨2, by decide⟩), opAt 3009 (.Dup ⟨12, by decide⟩),
   opAt 3010 .AND, opAt 3011 .XOR, opAt 3012 (.Swap ⟨1, by decide⟩),
   opAt 3013 .POP, opAt 3014 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3015 (.Dup ⟨2, by decide⟩), pushAt 3016 1 0x0b, opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨2, by decide⟩), opAt 3019 .POP, pushAt 3020 2 0x1432,
   opAt 3021 .JUMP]


@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2864 = 4935 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2865 = 4936 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2866 = 4937 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2867 = 4938 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2868 = 4939 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2869 = 4940 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2870 = 4941 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2871 = 4942 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2872 = 4943 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2873 = 4944 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2874 = 4947 := by rfl

@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2903 = 5005 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2904 = 5006 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2905 = 5039 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2906 = 5072 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2907 = 5105 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2908 = 5138 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2909 = 5139 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2910 = 5140 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2911 = 5141 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2912 = 5142 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2913 = 5143 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2914 = 5144 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2915 = 5145 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2916 = 5146 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2917 = 5147 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2918 = 5148 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2919 = 5149 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2920 = 5150 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2921 = 5151 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2922 = 5152 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2923 = 5153 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2924 = 5154 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2925 = 5155 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2926 = 5156 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2927 = 5157 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2928 = 5158 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2929 = 5159 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2930 = 5160 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2931 = 5162 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2932 = 5163 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2933 = 5165 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2934 = 5166 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2935 = 5169 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2936 = 5170 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2937 = 5171 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2938 = 5172 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2939 = 5173 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2940 = 5174 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2941 = 5175 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2942 = 5176 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2943 = 5177 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2944 = 5178 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2945 = 5179 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2946 = 5180 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2947 = 5182 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2948 = 5183 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2949 = 5185 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2950 = 5186 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2951 = 5187 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2952 = 5188 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2953 = 5189 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2954 = 5191 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2955 = 5192 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 2956 = 5193 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2957 = 5194 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2958 = 5195 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2959 = 5198 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 2960 = 5199 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 2961 = 5202 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 2962 = 5203 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 2963 = 5206 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2964 = 5207 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2965 = 5216 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2966 = 5218 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2967 = 5219 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2968 = 5220 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2969 = 5221 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2970 = 5222 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2971 = 5225 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2972 = 5226 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2973 = 5247 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2974 = 5248 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2975 = 5249 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2976 = 5251 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2977 = 5252 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2978 = 5253 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2979 = 5254 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2980 = 5255 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2981 = 5256 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 2982 = 5257 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2983 = 5258 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2984 = 5259 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2985 = 5260 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2986 = 5261 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2987 = 5262 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2988 = 5263 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2989 = 5264 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2990 = 5265 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2991 = 5266 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2992 = 5267 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2993 = 5269 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2994 = 5270 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 2995 = 5272 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 2996 = 5273 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 2997 = 5275 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 2998 = 5276 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 2999 = 5278 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3000 = 5279 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3001 = 5280 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3002 = 5282 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3003 = 5283 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3004 = 5284 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3005 = 5285 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3006 = 5286 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3007 = 5287 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3008 = 5288 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3009 = 5289 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3010 = 5290 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3011 = 5291 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3012 = 5292 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3013 = 5293 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3014 = 5294 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3015 = 5295 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3016 = 5296 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3017 = 5298 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3018 = 5299 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3019 = 5300 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3020 = 5301 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3021 = 5304 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
