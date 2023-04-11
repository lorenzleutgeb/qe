{
  description = "qe";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.11";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        base = "https://people.mpi-inf.mpg.de/~sturm/teaching/143421";

        pkgs = import nixpkgs { inherit system; };
        pyPkgs = pkgs.python310Packages;

        pyeda = with pyPkgs; buildPythonPackage rec {
            pname = "pyeda";
            version = "0.28.0";
            doCheck = false;
            src = fetchPypi {
              inherit pname version;
              hash = "sha256-BxhfRY1dCyulBY2ouV2tardoTOr0EjeiW80/AFSQ9Z0=";
            };
          };

        logic1 = with pyPkgs; buildPythonPackage rec {
            pname = "logic1";
            version = "0.1";
            doCheck = false;
            format = "wheel";
            src = pkgs.requireFile {
              url = "${base}/${pname}/${pname}-${version}-py3-none-any.whl";
              sha256 = "0l7ai7mc805ay2kxd380pl0zv40ndday15n252q9r1khh3f625by";
            };
            buildInputs = [ pyeda sympy typing-extensions ];
          };

      in rec {
        devShell = pkgs.mkShell {
          buildInputs = with pyPkgs; [
            pip
            mypy
            pytest
            jupyter
	    sympy
	    pyeda
	    logic1
          ];
          shellHook =
            "pip show logic1 pyeda sympy | grep -E 'Name|Version|Summary|Req|---'";
        };
      });
}
