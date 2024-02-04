use Utils; // initRuntime / deinitRuntime
use FFI;
use ForeignTypes;
use Vector;
use Timing;
use StatesEnumeration;

use CTypes;
use Time;
use JSON;
use IO;
// use LatticeSymmetries;
// use BlockToHashed;
// use HashedToBlock;
// use MyHDF5;
// use Time;

// config const kHamiltonian = "data/heisenberg_kagome_12.yaml";
// config const kRepresentatives = "data/heisenberg_kagome_12.h5";

proc test_basis() {
  const basis = new Basis("{ \"number_spins\": 4, \"hamming_weight\": 2 }");
  assert(basis.info.number_sites == 4);
  assert(basis.info.hamming_weight == 2);
  assert(basis.info.spin_inversion == 0);
  assert(basis.info.number_up == 2);
  assert(basis.info.has_permutation_symmetries == false);
  assert(basis.info.particle_type == LS_HS_SPIN);
  const basisPtr = c_addrOfConst(basis);
  const infoPtr = c_addrOfConst(basis.info);

  coforall i in 0 ..# 10 with (in basis) {
    const myBasisPtr = c_addrOfConst(basis);
    const myInfoPtr = c_addrOfConst(basis.info);
    // we created a copy of basis, so it should point to another memory location
    assert(myBasisPtr != basisPtr);
    // since we're on one locale, the copy constructor should have shared the underlying ls_hs_basis, so
    // the info fields should point to the same memory location
    assert(myInfoPtr == infoPtr);
  }
}

proc test_determineEnumerationRanges() {
  const basis1 = new Basis("{ \"number_spins\": 4, \"hamming_weight\": 2 }");
  const ref basisInfo1 = basis1.info;

  assert(determineEnumerationRanges(basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate,
                                    1, basisInfo1).equals([3 .. 12,]));
  assert(determineEnumerationRanges(basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate,
                                    2, basisInfo1).equals([3 .. 6, 9 .. 12]));
  assert(determineEnumerationRanges(basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate,
                                    3, basisInfo1).equals([3 .. 5, 6 .. 9, 10 .. 12]));
  assert(determineEnumerationRanges(basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate,
                                    4, basisInfo1).equals([3 .. 5, 6 .. 6, 9 .. 10, 12 .. 12]));
  assert(determineEnumerationRanges(basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate,
                                    6, basisInfo1).equals([3 .. 3, 5 .. 5, 6 .. 6, 9 .. 9, 10 .. 10, 12 .. 12]));
  assert(determineEnumerationRanges(basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate,
                                    10, basisInfo1).equals([3 .. 3, 5 .. 5, 6 .. 6, 9 .. 9, 10 .. 10, 12 .. 12]));

  const basis2 = new Basis("{ \"number_spins\": 4, \"hamming_weight\": null }");
  const ref basisInfo2 = basis2.info;

  assert(determineEnumerationRanges(basisInfo2.min_state_estimate .. basisInfo2.max_state_estimate,
                                    1, basisInfo2).equals([0 .. 15,]));
  assert(determineEnumerationRanges(basisInfo2.min_state_estimate .. basisInfo2.max_state_estimate,
                                    2, basisInfo2).equals([0 .. 7, 8 .. 15]));

  const basis3 = new Basis("{ \"number_spins\": 36, \"hamming_weight\": 18 }");
  const ref basisInfo3 = basis3.info;
  var t3 = new stopwatch();
  t3.start();
  const rs = determineEnumerationRanges(basisInfo3.min_state_estimate .. basisInfo3.max_state_estimate,
                                        10000, basisInfo3);
  t3.stop();
  assert(t3.elapsed() < 0.1);
  assert(rs.size == 10000);

  for loc in Locales do on loc {
    stdout.withSerializer(new jsonSerializer()).writeln(summarize());
  }
}


const smallBasesJsonDefs = [
  "{ \"number_spins\": 1 }",
  "{ \"number_spins\": 1, \"hamming_weight\": 0 }",
  "{ \"number_spins\": 1, \"hamming_weight\": 1 }",
  // "{ \"number_spins\": 2, \"spin_inversion\": 1 }", // TODO: fix me !!!
];
const smallBasesExpectedStates = [
  new Vector([0:uint, 1:uint]),
  new Vector([0:uint]),
  new Vector([1:uint]),
  // new Vector([1:uint]), // TODO: fix me !!!
];
const smallBasesExpectedNorms = [
  new Vector([1.0, 1.0]),
  new Vector([1.0]),
  new Vector([1.0]),
  // new Vector([0.5]), // TODO: fix me !!!
];

proc checkArraysEqual(arr1 : [] ?eltType, arr2 : [] eltType) {
  if !arr1.equals(arr2) {
    writeln("Failed: arrays differ:");
    var count = 0;
    const maxCount = 10;
    for (i, x1, x2) in zip(arr1.domain, arr1, arr2) {
      if x1 != x2 {
        if count >= maxCount {
          writeln("...");
          break;
        }
        writeln(i, ": ", x1, " != ", x2);
        count += 1;
      }
    }
    halt("checkArraysEqual test failed");
  }
}

proc test__enumerateStatesGeneric() {
  const basis1 = new Basis("{ \"number_spins\": 5, \"hamming_weight\": 2 }");
  const ref basisInfo1 = basis1.info;
  const r1 = basisInfo1.min_state_estimate .. basisInfo1.max_state_estimate;
  var bucket1 = new Bucket();
  _enumerateStatesGeneric(r1, basis1, bucket1.basisStates, bucket1.norms);
  writeln(bucket1.basisStates.toArray());
  writeln(bucket1.norms.toArray());

  for (basisDef, expectedStates, expectedNorms)
      in zip(smallBasesJsonDefs, smallBasesExpectedStates, smallBasesExpectedNorms) {

    const b = new Basis(basisDef);
    const r = b.info.min_state_estimate .. b.info.max_state_estimate;
    var s = new Vector(uint(64));
    var n = new Vector(real(64));
    _enumerateStatesGeneric(r, b, s, n);

    checkArraysEqual(s.toArray(), expectedStates.toArray());
    checkArraysEqual(n.toArray(), expectedNorms.toArray());
  }
}

proc test_enumerateStates() {
  const basis1 = new Basis("{ \"number_spins\": 5, \"hamming_weight\": 2 }");
  const rs = determineEnumerationRanges(basis1.info.min_state_estimate .. basis1.info.max_state_estimate,
                                        4, basis1.info);
  var basisStates;
  var norms;
  enumerateStates(rs, basis1, basisStates, norms);
  writeln(basisStates);
  writeln(norms);

  const basis2 = new Basis("{ \"number_spins\": 3, \"hamming_weight\": 1 }");
  const rs2 = determineEnumerationRanges(basis2.info.min_state_estimate .. basis2.info.max_state_estimate, 4, basis2.info);
  var basisStates2;
  var norms2;
  enumerateStates(rs2, basis2, basisStates2, norms2);
  writeln(basisStates2);
  writeln(norms2);
}

record Foo {
  var xs : c_array(int, 5);
}

proc bar(x : c_ptr(int)) {
  x[0] = 10;
}

proc test_something() {
  var foo = new Foo();
  writeln(foo.xs);
  bar(foo.xs:c_ptr(int));
  writeln(foo.xs);

  var raw : c_array(int, 5);
  writeln(raw);
  bar(raw);
  writeln(raw);
}

proc main() {
  initRuntime();
  defer deinitRuntime();

  test_basis();
  test_determineEnumerationRanges();
  test__enumerateStatesGeneric();
  test_enumerateStates();
  test_something();

  // const basis = loadConfigFromYaml(kHamiltonian);

  // var timer = new stopwatch();
  // timer.start();
  // const masks;
  // const basisStates = enumerateStates(basis, masks);
  // timer.stop();

  // const predicted = arrFromHashedToBlock(basisStates, masks);
  // const reference =
  //   readDatasetAsBlocks(kRepresentatives, "/representatives",
  //                       rank = 1, eltType = uint(64));

  // const theSame = && reduce [i in reference.domain] reference[i] == predicted[i];
  // if !theSame {
  //   var maxErrorCount = 10;
  //   for i in reference.domain {
  //     if reference[i] != predicted[i] && maxErrorCount > 0 {
  //       writeln("at index ", i, ": ", reference[i], " != ", predicted[i]);
  //       maxErrorCount -= 1;
  //     }
  //   }
  // }
  // writeln(timer.elapsed());
  return 0;
}
