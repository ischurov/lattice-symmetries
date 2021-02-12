// Copyright (c) 2019-2020, Tom Westerhout
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice, this
//   list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above copyright notice,
//   this list of conditions and the following disclaimer in the documentation
//   and/or other materials provided with the distribution.
//
// * Neither the name of the copyright holder nor the names of its
//   contributors may be used to endorse or promote products derived from
//   this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#ifndef LATTICE_SYMMETRIES_H
#define LATTICE_SYMMETRIES_H

#define LATTICE_SYMMETRIES_UNREACHABLE __builtin_unreachable()
#define LATTICE_SYMMETRIES_LIKELY(x) __builtin_expect(x, 1)
#define LATTICE_SYMMETRIES_UNLIKELY(x) __builtin_expect(x, 0)
#define LATTICE_SYMMETRIES_EXPORT __attribute__((visibility("default")))
#define LATTICE_SYMMETRIES_NORETURN __attribute__((noreturn))

#if !defined(LATTICE_SYMMETRIES_FORCEINLINE)
#    if defined(_MSC_VER)
#        define LATTICE_SYMMETRIES_FORCEINLINE __forceinline
#    elif defined(__GNUC__) && __GNUC__ > 3 // Clang also defines __GNUC__ (as 4)
#        define LATTICE_SYMMETRIES_FORCEINLINE inline __attribute__((__always_inline__))
#    else
#        define LATTICE_SYMMETRIES_FORCEINLINE inline
#    endif
#endif

#if !defined(LATTICE_SYMMETRIES_NOINLINE)
#    if defined(_MSC_VER)
#        define LATTICE_SYMMETRIES_NOINLINE __declspec(noinline)
#    elif defined(__GNUC__) && __GNUC__ > 3 // Clang also defines __GNUC__ (as 4)
#        if defined(__CUDACC__)             // nvcc doesn't always parse __noinline__,
#            define LATTICE_SYMMETRIES_NOINLINE __attribute__((noinline))
#        else
#            define LATTICE_SYMMETRIES_NOINLINE __attribute__((__noinline__))
#        endif
#    else
#        define LATTICE_SYMMETRIES_NOINLINE
#    endif
#endif

#if defined(__AVX2__)
#    define LATTICE_SYMMETRIES_HAS_AVX2() 1
#else
#    define LATTICE_SYMMETRIES_HAS_AVX2() 0
#endif

#if defined(__AVX__)
#    define LATTICE_SYMMETRIES_HAS_AVX() 1
#else
#    define LATTICE_SYMMETRIES_HAS_AVX() 0
#endif

#if defined(__SSE4_1__) && defined(__SSE4_2__)
#    define LATTICE_SYMMETRIES_HAS_SSE4() 1
#else
#    define LATTICE_SYMMETRIES_HAS_SSE4() 0
#endif

#if !defined(__SSE2__) && !defined(__x86_64__)
#    error "unsupported architecture; lattice-symmetries currently only works on x86_64"
#endif

#if defined(__cplusplus)
#    include <cstdint>
#else
#    include <stdbool.h>
#    include <stdint.h>
#endif

#if defined(__cplusplus)
extern "C" {
#endif

/// \defgroup errors Error handling
/// \brief Status codes and corresponding utility functions
///
/// LatticeSymmetries library uses status codes for reporting errors. #ls_error_code specifies all
/// possible status codes which can be returned by library functions. Names of the constants should
/// explain errors pretty well, however for higher-level wrappers it is useful to convert these
/// status codes to human-readable messages. #ls_error_to_string function provides this
/// functionality.
///
/// \note Even though internally the library is written in C++17, exceptions are disabled during
///       compilation. I.e. we never throw exceptions, all errors are reported using status codes.
///
/// @{

/// \brief Status codes used by the library
///
typedef enum ls_error_code {
    LS_SUCCESS = 0,             ///< No error
    LS_OUT_OF_MEMORY,           ///< Memory allocation failed
    LS_INVALID_ARGUMENT,        ///< Argument to a function is invalid
    LS_INVALID_HAMMING_WEIGHT,  ///< Invalid Hamming weight
    LS_INVALID_SPIN_INVERSION,  ///< Invalid value for spin_inversion
    LS_INVALID_NUMBER_SPINS,    ///< Invalid number of spins
    LS_INVALID_PERMUTATION,     ///< Argument is not a valid permutation
    LS_INVALID_SECTOR,          ///< Sector exceeds the periodicity of the operator
    LS_INVALID_STATE,           ///< Invalid basis state
    LS_INVALID_DATATYPE,        ///< Invalid datatype
    LS_PERMUTATION_TOO_LONG,    ///< Such long permutations are not supported
    LS_INCOMPATIBLE_SYMMETRIES, ///< Symmetries are incompatible
    LS_NOT_A_REPRESENTATIVE,    ///< Spin configuration is not a representative
    LS_WRONG_BASIS_TYPE,        ///< Expected a basis of different type
    LS_CACHE_NOT_BUILT,         ///< List of representatives is not yet built
    LS_COULD_NOT_OPEN_FILE,     ///< Failed to open file
    LS_FILE_IO_FAILED,          ///< File input/output failed
    LS_CACHE_IS_CORRUPT,        ///< File does not contain a list of representatives
    LS_OPERATOR_IS_COMPLEX,     ///< Trying to apply complex operator to real vector
    LS_DIMENSION_MISMATCH,      ///< Operator dimension does not match vector length
    LS_SYSTEM_ERROR,            ///< Unknown error
} ls_error_code;

char const* ls_error_to_string(ls_error_code code);
void        ls_destroy_string(char const* message);

typedef void (*ls_error_handler)(char const* expr, char const* file, unsigned line,
                                 char const* function, char const* msg);

void ls_set_check_fail_handler(ls_error_handler func);
void ls_set_assert_fail_handler(ls_error_handler func);

LATTICE_SYMMETRIES_NORETURN
void ls_assert_fail(char const* expr, char const* file, unsigned line, char const* function,
                    char const* msg);

LATTICE_SYMMETRIES_NORETURN
void ls_check_fail(char const* expr, char const* file, unsigned line, char const* function,
                   char const* msg);

#define LATTICE_SYMMETRIES_CHECK(cond, msg)                                                        \
    (LATTICE_SYMMETRIES_LIKELY(cond)                                                               \
         ? ((void)0)                                                                               \
         : ls_check_fail(#cond, __FILE__, __LINE__, __FUNCTION__, msg))

#if !defined(NDEBUG)
#    define LATTICE_SYMMETRIES_ASSERT(cond, msg)                                                   \
        (LATTICE_SYMMETRIES_LIKELY(cond)                                                           \
             ? ((void)0)                                                                           \
             : ls_assert_fail(#cond, __FILE__, __LINE__, __FUNCTION__, msg))
#else
#    define LATTICE_SYMMETRIES_ASSERT(cond, msg) ((void)0)
#endif

/// @}
// end of errors group

bool ls_is_logging_enabled();
void ls_enable_logging();
void ls_disable_logging();

bool ls_has_avx2();
bool ls_has_avx();
bool ls_has_sse4();

#define LATTICE_SYMMETRIES_DISPATCH(func, ...)                                                     \
    if (ls_has_avx2()) { return ::lattice_symmetries::avx2::func(__VA_ARGS__); }                   \
    if (ls_has_avx()) { return ::lattice_symmetries::avx::func(__VA_ARGS__); }                     \
    if (ls_has_sse4()) { return ::lattice_symmetries::sse4::func(__VA_ARGS__); }                   \
    return ::lattice_symmetries::sse2::func(__VA_ARGS__)

// This is an internal function!
void ls_private_log_debug(char const* file, unsigned line, char const* function, char const* fmt,
                          ...);

#define LATTICE_SYMMETRIES_LOG_DEBUG(fmt, ...)                                                     \
    ls_private_log_debug(__FILE__, __LINE__, __FUNCTION__, fmt, __VA_ARGS__)

typedef uint64_t ls_bits64;

typedef struct ls_bits512 {
    ls_bits64 words[8];
} ls_bits512;

/// \defgroup symmetries Symmetries
/// \brief Working with individual symmetries
///
/// @{

/// \brief Symmetry operator
///
/// All lattice symmetries are built from two primitive operations: permutation and spin inversion.
/// Furthermore, each symmetry has corresponding eigenvalue to which we restrict the Hilbert space.
typedef struct ls_symmetry ls_symmetry;

/// \brief Allocates and constructs a symmetry.
///
/// \warning #ls_symmetry must be destructed and deallocated using #ls_destroy_symmetry.
///
/// \param ptr upon successful completion \p ptr set to point to the newly constructed object. Must
///            not be `nullptr`. In case of error, \p ptr is untouched.
/// \param length length of the \p permutation array. Must not exceed 512.
/// \param permutation permutation of `{0, 1, ..., length - 1}`.
/// \param flip whether application of this symmetry inverts spins.
/// \param sector symmetry sector to which we restrict the problem. It must be between zero
//                (inclusive) and periodicity of the symmetry operator (exclusive).
/// \return #LS_SUCCESS on successful completion. #LS_NOT_A_PERMUTATION if \p permutation does not
///         form a valid permutation. #LS_PERMUTATION_TOO_LONG if \p length exceeds 512.
///         #LS_INVALID_SECTOR if \p sector exceeds the periodicity of the symmetry.
/// \see #ls_destroy_symmetry
ls_error_code ls_create_symmetry(ls_symmetry** ptr, unsigned length, unsigned const permutation[],
                                 unsigned sector);
/// \brief Destructs and deallocates the symmetry.
///
/// This function **must** be called on objects constructed using #ls_create_symmetry.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \see #ls_create_symmetry
void ls_destroy_symmetry(ls_symmetry* symmetry);
/// \brief Get symmetry sector.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \return symmetry sector.
/// \see #ls_get_flip, #ls_get_phase, #ls_get_periodicity, #ls_get_eigenvalue
unsigned ls_get_sector(ls_symmetry const* symmetry);
/// \brief Get whether the symmetry applies spin inversion.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \return `true` if \p symmetry applies spin inversion.
/// \see #ls_get_sector, #ls_get_phase, #ls_get_periodicity, #ls_get_eigenvalue
// bool ls_get_flip(ls_symmetry const* symmetry);
/// \brief Get phase of the eigenvalue.
///
/// Phase is simply `sector / periodicity`. This function is provided for convenience only.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \return complex phase of the eigenvalue of \p symmetry.
/// \see #ls_get_sector, #ls_get_flip, #ls_get_periodicity, #ls_get_eigenvalue
double ls_get_phase(ls_symmetry const* symmetry);
/// \brief Get eigenvalue of the symmetry.
///
/// Eigenvalue is written to \p out.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \param out pointer to `std::complex<double>` or any other structure binary compatible
///            with it (e.g. `double _Complex` or `double[2]`). Must not be `nullptr`.
/// \see #ls_get_sector, #ls_get_flip, #ls_get_phase, #ls_get_periodicity
void ls_get_eigenvalue(ls_symmetry const* symmetry, void* out);
/// \brief Get periodicity of the symmetry.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \return periodicity of the symmetry.
/// \see #ls_get_sector, #ls_get_flip, #ls_get_phase, #ls_get_eigenvalue
unsigned ls_get_periodicity(ls_symmetry const* symmetry);
/// \brief Apply symmetry to a spin configuration.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \param bits spin configuration. It is modified in-place. Size of \p bits array is at least
///             `ceil(number_spins / 64)`. `i`'th spin is determined as `(bits[i / 64] >> (i % 64)) & 0x1`.
/// \see #ls_get_number_spins
void ls_apply_symmetry(ls_symmetry const* symmetry, ls_bits512* bits);

/// \brief Get number of spins in the system.
///
/// \param symmetry pointer to symmetry. Must not be `nullptr`.
/// \return number of spins for which the symmetry was constructed.
/// \see #ls_apply_symmetry
unsigned ls_symmetry_get_number_spins(ls_symmetry const* symmetry);

/// @}
// end of symmetries group

/// \defgroup group Group
/// \brief Defining symmetry groups
///
/// @{

/// \brief Opaque structure representing a symmetry group.
///
/// This is basically a collection of #ls_symmetry which is closed under symmetry composition
/// operation (**TODO**: make symmetry composition part of public interface).
typedef struct ls_group ls_group;

/// \brief Allocates and constructs a symmetry group.
///
/// After successful completion of this function \p ptr points to the newly constructed
/// #ls_group.
///
/// \note #ls_group must be destructed and deallocated using #ls_destroy_group.
///
/// \param ptr after success \p ptr is set to point to the newly constructed object. In case of
///            error, \p ptr is untouched.
/// \param size length of the \p generators array.
/// \param generators array of pointers to individual symmetries which act as group generators.
/// \return #LS_SUCCESS on successful completion. #LS_INCOMPATIBLE_SYMMETRIES if some symmetries are
///         incompatible with each other.
/// \see #ls_destroy_group
ls_error_code ls_create_group(ls_group** ptr, unsigned size, ls_symmetry const* generators[]);
ls_error_code ls_create_trivial_group(ls_group** ptr, unsigned number_spins);
/// \brief Destructs and deallocates the symmetry group.
///
/// This function **must** be called on objects constructed using #ls_create_group.
///
/// \param group pointer to the group. Must not be `nullptr`.
/// \see #ls_create_group
void ls_destroy_group(ls_group* group);
/// \brief Get size of the symmetry sector.
///
/// \param group pointer to symmetry group. Must not be `nullptr`.
/// \return number of elements in the group.
unsigned ls_get_group_size(ls_group const* group);

ls_symmetry const* ls_group_get_symmetries(ls_group const* group);

// Return value -1 means that the group is empty and number of spins could not be determined
int ls_group_get_number_spins(ls_group const* group);

/// @}
// end of group group

/// \defgroup basis Spin basis
/// \brief Working with Hilbert space bases
///
/// @{

/// \brief Basis for a Hilbert space consisting of `N` spins.
typedef struct ls_spin_basis ls_spin_basis;

/// \brief Opaque structure representing a vector of representative basis states.
typedef struct ls_states ls_states;

/// \brief Allocates and constructs a basis.
///
/// After successful completion of this function \p ptr points to the newly constructed
/// #ls_spin_basis.
///
/// \note #ls_spin_basis must be destructed and deallocated using #ls_destroy_spin_basis.
///
/// \param ptr is set to point to the newly constructed object.
/// \param group symmetry group. Group may be empty, but must not be `nullptr`.
/// \param number_spins number of spins in the system. When \p group is not empty, number of spins
///                     may be deduced from it. Deduced number of spins must match the value of \p
///                     number_spins.
/// \param hamming_weight allows to restrict to a sector with particular magnetisation. Hamming
///                       weight is the number of spins pointing upward. If one does not wish to
///                       restrict to a sector with given magnetisation, \p hamming_weight should
///                       be set to `-1`.
/// \return #LS_SUCCESS upon success; #LS_INVALID_HAMMING_WEIGHT if \p hamming_weight exceeds \p
///         number_spins or has a negative value other than `-1`; #LS_INVALID_NUMBER_SPINS if number
///         of spins does not match the one deduced from \p group.
/// \see #ls_destroy_spin_basis, #ls_copy_spin_basis
ls_error_code ls_create_spin_basis(ls_spin_basis** ptr, ls_group const* group,
                                   unsigned number_spins, int hamming_weight, int spin_inversion);
/// \brief Create a shallow copy of \p basis.
///
/// \see #ls_create_spin_basis, #ls_destroy_spin_basis
ls_spin_basis* ls_copy_spin_basis(ls_spin_basis const* basis);
/// \brief Destructs and deallocates a #ls_spin_basis.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \see #ls_create_spin_basis, #ls_copy_spin_basis
void ls_destroy_spin_basis(ls_spin_basis* basis);
/// \brief Get number of spins in the system.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \return number of spins in the system.
/// \see #ls_get_number_states, #ls_get_hamming_weight, #ls_get_state_info, #ls_get_index, #ls_get_states
unsigned ls_get_number_spins(ls_spin_basis const* basis);
/// \brief Get number of bits which is used to represent a spin configuration.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \return 64 or 512 depending on system size.
unsigned ls_get_number_bits(ls_spin_basis const* basis);
/// \brief Get Hamming weight of all basis states.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \return a non-negative Hamming weight or `-1` if any Hamming weight is allowed.
/// \see #ls_get_number_spins, #ls_get_number_states, #ls_get_state_info, #ls_get_index, #ls_get_states
int ls_get_hamming_weight(ls_spin_basis const* basis);
int ls_get_spin_inversion(ls_spin_basis const* basis);
/// \brief Return whether the basis is restricted to some symmetry sector.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \return `true` if the basis was constructed with a non-empty #ls_group and `false` otherwise.
bool ls_has_symmetries(ls_spin_basis const* basis);
/// \brief Get number of states in the basis (i.e. dimension of the Hilbert space).
///
/// \warning This operation is supported only *after* a call to #ls_build.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \param out on success, \p out is set to the number of states.
/// \return #LS_SUCCESS on success and #LS_CACHE_NOT_BUILT if basis has not been built beforehand.
/// \see #ls_build
ls_error_code ls_get_number_states(ls_spin_basis const* basis, uint64_t* out);
/// \brief Construct list of all representatives.
///
/// \note This operation is supported only for small systems.
///
/// After a call to this function operations like #ls_get_index and #ls_get_number_states become
/// available.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \return #LS_SUCCESS on success or other status code on error.
ls_error_code ls_build(ls_spin_basis* basis);
ls_error_code ls_build_unsafe(ls_spin_basis* basis, uint64_t size,
                              uint64_t const representatives[]);
/// \brief Get information about a spin configuration.
///
/// Given a spin configuration, computes its representative, character, and norm of the orbit.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \param bits spin configuration. Size of \p bits array is 8 (i.e. 512 bits). If number of spins
///             in the basis is fewer than 64, then only the first word of \p bits will be accessed.
/// \param representative where the representative will be written to. Same as with \p bits, when
///        the number of spins does not exceed 64, only the first word of \p representative will be
///        modified.
/// \param character a pointer to `std::complex<double>` (`_Complex double` in C) where the
///                  character will be written to.
/// \param norm where the norm of the orbit will be written to.
void ls_get_state_info(ls_spin_basis const* basis, ls_bits512 const* bits,
                       ls_bits512* representative, void* character, double* norm);
/// \brief Get index of a basis representative.
///
/// \note \p bits must be a basis representative. If you just have a spin configuration, call
///       #ls_get_state_info first to obtain its representative.
///
/// \warning This operation is supported only *after* a call to #ls_build.
///
/// \param basis pointer to Hilbert space basis. Must not be `nullptr`.
/// \param bits basis representative. Since this function only works for small systems, \p bits has
///             length 1.
ls_error_code ls_get_index(ls_spin_basis const* basis, uint64_t bits, uint64_t* index);

// NOLINTNEXTLINE(modernize-use-trailing-return-type)
ls_error_code ls_get_states(ls_states** ptr, ls_spin_basis const* basis);
void          ls_destroy_states(ls_states* states);
// NOLINTNEXTLINE(modernize-use-trailing-return-type)
uint64_t const* ls_states_get_data(ls_states const* states);
// NOLINTNEXTLINE(modernize-use-trailing-return-type)
uint64_t ls_states_get_size(ls_states const* states);

// NOLINTNEXTLINE(modernize-use-trailing-return-type)
ls_error_code ls_save_cache(ls_spin_basis const* basis, char const* filename);
// NOLINTNEXTLINE(modernize-use-trailing-return-type)
ls_error_code ls_load_cache(ls_spin_basis* basis, char const* filename);

/// @}
// end of group basis

// NOLINTNEXTLINE(modernize-use-using)
typedef struct ls_interaction ls_interaction;
// NOLINTNEXTLINE(modernize-use-using)
typedef struct ls_operator ls_operator;

ls_error_code ls_create_interaction1(ls_interaction** ptr, void const* matrix_2x2,
                                     unsigned number_nodes, uint16_t const* nodes);

ls_error_code ls_create_interaction2(ls_interaction** ptr, void const* matrix_4x4,
                                     unsigned number_edges, uint16_t const (*edges)[2]);

ls_error_code ls_create_interaction3(ls_interaction** ptr, void const* matrix_8x8,
                                     unsigned number_triangles, uint16_t const (*triangles)[3]);

ls_error_code ls_create_interaction4(ls_interaction** ptr, void const* matrix_16x16,
                                     unsigned number_plaquettes, uint16_t const (*plaquettes)[4]);

void ls_destroy_interaction(ls_interaction* interaction);

bool ls_interaction_is_real(ls_interaction const* interaction);

uint64_t ls_interaction_max_buffer_size(ls_interaction const* interaction);

ls_error_code ls_create_operator(ls_operator** ptr, ls_spin_basis const* basis,
                                 unsigned number_terms, ls_interaction const* const terms[]);
void          ls_destroy_operator(ls_operator* op);

typedef enum {
    LS_FLOAT32,
    LS_FLOAT64,
    LS_COMPLEX64,
    LS_COMPLEX128,
} ls_datatype;

typedef ls_error_code (*ls_callback)(ls_bits512 const* bits, void const* coeff, void* cxt);

ls_error_code ls_operator_apply(ls_operator const* op, ls_bits512 const* bits, ls_callback func,
                                void* cxt);

ls_error_code ls_operator_matmat(ls_operator const* op, ls_datatype dtype, uint64_t size,
                                 uint64_t block_size, void const* x, uint64_t x_stride, void* y,
                                 uint64_t y_stride);

ls_error_code ls_operator_expectation(ls_operator const* op, ls_datatype dtype, uint64_t size,
                                      uint64_t block_size, void const* x, uint64_t x_stride,
                                      void* out);

uint64_t ls_operator_max_buffer_size(ls_operator const* op);

bool ls_operator_is_real(ls_operator const* op);

#if defined(__cplusplus)
} // extern "C"
#endif

#if defined(__cplusplus)
#    include <system_error>

namespace std {
template <> struct is_error_code_enum<ls_error_code> : true_type {};
} // namespace std

namespace lattice_symmetries {
class ls_error_category : public std::error_category {
  public:
    [[nodiscard]] auto name() const noexcept -> const char* final;
    [[nodiscard]] auto message(int c) const -> std::string final;
};
auto get_error_category() noexcept -> ls_error_category const&;
} // namespace lattice_symmetries

inline auto make_error_code(ls_error_code const e) noexcept -> std::error_code
{
    return {static_cast<int>(e), lattice_symmetries::get_error_category()};
}
#endif

#endif // LATTICE_SYMMETRIES_H
