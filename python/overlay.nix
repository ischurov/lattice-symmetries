{ version
}:

final: prev: {
  pythonPackagesExtensions = prev.pythonPackagesExtensions ++ [
    (python-final: python-prev: {
      grip = python-prev.grip.overrideAttrs (attrs: {
        src = final.fetchFromGitHub {
          owner = "Antonio-R1";
          repo = "grip";
          rev = "d2efd3c6a896c01cfd7624b6504107e7b3b4b20f";
          hash = "sha256-0wgIM7Ll5WELvAOiu1TLyoNSrhJ22Y1SRbWqa3BDF3k=";
        };
        checkPhase = "true";
        installCheckPhase = "true";
      });
      lattice-symmetries = python-final.buildPythonPackage rec {
        pname = "lattice-symmetries";
        inherit version;
        src = ./.;

        buildInputs = with prev; [
          lattice-symmetries.kernels_v2
          lattice-symmetries.haskell
          # lattice-symmetries.chapel
        ];
        propagatedBuildInputs = with python-final; [
          cffi
          loguru
          numpy
          scipy
        ];

        nativeCheckInputs = with python-final; [
          pip
          pytestCheckHook
          igraph
        ];

        postPatch = ''
          awk '/python-cffi: START/{flag=1;next}/python-cffi: STOP/{flag=0}flag' \
            ${prev.lattice-symmetries.kernels_v2}/include/lattice_symmetries_types.h \
            >lattice_symmetries/extracted_declarations.h
          awk '/python-cffi: START/{flag=1;next}/python-cffi: STOP/{flag=0}flag' \
            ${prev.lattice-symmetries.haskell}/include/lattice_symmetries_functions.h \
            >>lattice_symmetries/extracted_declarations.h
        '';

        preCheck = "rm -rf lattice_symmetries";

        checkPhase = ''
          runHook preCheck
          export LS_TEST_DATA=${prev.lattice-symmetries.test-data}/share/data/matvec
          python3 -m pytest --color=yes --capture=no test/test_api.py | tee output.txt
          grep -q -E '(FAILURES|failed)' output.txt && exit 1
          runHook postCheck
        '';

        preShellHook = ''
          if test -e setup.py; then
            rm -rf build/ lattice_symmetries/*.so
            ${postPatch}
          fi
        '';

      };
    })
  ];
  lattice-symmetries = (prev.lattice-symmetries or { }) // {
    python = prev.python3Packages.lattice-symmetries;
  };
}
