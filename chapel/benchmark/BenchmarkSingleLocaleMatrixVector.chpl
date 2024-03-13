import Timing;
use CSR;
use ForeignTypes;
use MatrixVectorProduct;
use StatesEnumeration;
use Utils;

import Random;
use IO;
use JSON;
use Time;

config const kHamiltonian = "../test/random_quspin/test_4_2_10_10_expr.json";
config const kRepeat = 1;
config const kRandomSeed = 42;

proc main() {
  initRuntime();
  defer deinitRuntime();

  var timer = new stopwatch();
  timer.start();
  const matrix = loadOperatorFromFile(kHamiltonian);
  timer.stop();

  logDebug("loading took ", timer.elapsed());
  logDebug(matrix.max_number_off_diag);
  // Pre-compile
  const _kernel = ls_chpl_get_state_to_index_kernel(matrix.basis.payload);

  const basisStates, norms, keys;
  enumerateStates(matrix.basis, basisStates, norms, keys);
  const ref states = basisStates[here];

  var x : [0 ..# states.size] complex(128);
  var y : [0 ..# states.size] complex(128);

  Random.fillRandom(x, seed = kRandomSeed);

  var times : [0 ..# kRepeat] real;
  for k in 0 ..# kRepeat {
    timer.reset();
    timer.start();

    perLocaleMatrixVector(matrix, x, y, states, norms[here]);

    timer.stop();
    times[k] = timer.elapsed();
  }

  writeln(times);

  y = 0;

  timer.reset();
  timer.start();
  const csrMatrix = convertOffDiagToCsr(matrix, complex(128), states, norms[here]);
  const diag = extractDiag(matrix, complex(128), states, norms[here]);
  timer.stop();
  writeln(timer.elapsed());

  times = 0;
  for k in 0 ..# kRepeat {
    timer.reset();
    timer.start();

    csrMatvec(csrMatrix, safe_c_ptrToConst(x), safe_c_ptrTo(y));
    y += diag * x;

    timer.stop();
    times[k] = timer.elapsed();
  }

  writeln(times);
}
