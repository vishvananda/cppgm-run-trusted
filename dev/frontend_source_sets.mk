# Per-tool implementation source lists for the compiler.
#
# Add dev/src/foo.cpp to the tools that use it by adding `foo` below. For
# subdirectories, use the path without `.cpp`, such as `parser/foo`.

FRONTEND_SOURCE_SET_TARGETS := abimangle pptoken posttoken ctrlexpr macro preproc recog nsdecl nsinit cy86 cppgm++ lowiropt lowir2cy86 lowir2native

FRONTEND_OBJ_BASENAMES_abimangle :=
FRONTEND_OBJ_BASENAMES_pptoken := pptoken_lib
FRONTEND_OBJ_BASENAMES_posttoken := pptoken_lib pp_token posttoken_support posttoken_pipeline
FRONTEND_OBJ_BASENAMES_ctrlexpr := pptoken_lib pp_token posttoken_support ctrlexpr_support
FRONTEND_OBJ_BASENAMES_macro := pptoken_lib pp_token posttoken_support posttoken_pipeline macro_support
FRONTEND_OBJ_BASENAMES_preproc := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support
FRONTEND_OBJ_BASENAMES_recog := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support recog_grammar recog_support
FRONTEND_OBJ_BASENAMES_nsdecl := pptoken_lib pp_token posttoken_support posttoken_pipeline ctrlexpr_support macro_support preproc_support nsdecl_model nsdecl_parser nsdecl_support
FRONTEND_OBJ_BASENAMES_nsinit :=
FRONTEND_OBJ_BASENAMES_cy86 :=
FRONTEND_OBJ_BASENAMES_cppgm++ :=
FRONTEND_OBJ_BASENAMES_lowiropt :=
FRONTEND_OBJ_BASENAMES_lowir2cy86 :=
FRONTEND_OBJ_BASENAMES_lowir2native :=
