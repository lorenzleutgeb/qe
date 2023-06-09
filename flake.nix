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

        pyeda = with pyPkgs;
          buildPythonPackage rec {
            pname = "pyeda";
            version = "0.28.0";
            doCheck = false;
            src = fetchPypi {
              inherit pname version;
              hash = "sha256-BxhfRY1dCyulBY2ouV2tardoTOr0EjeiW80/AFSQ9Z0=";
            };
          };

        logic1 = with pyPkgs;
          buildPythonPackage rec {
            pname = "logic1";
            version = "0.1.1";
            doCheck = false;
            format = "wheel";
            src = pkgs.requireFile {
              url = "${base}/${pname}/${pname}-${version}-py3-none-any.whl";
              sha256 = "1piccy7y9ghlmk0qhb3hvlj1qnjy0vk2jd22ng27lss4h7vm22sd";
            };
            buildInputs = [ pyeda sympy typing-extensions ];
          };

        flameprof = pyPkgs.buildPythonPackage rec {
          pname = "flameprof";
          version = "0.4";
          src = pyPkgs.fetchPypi {
            inherit version;
            inherit pname;
            hash = "sha256-28htQZDLu6Yk8eCkD0TZ25YTjidTTYPI70LUIIV4daM=";
          };
        };

        pyflame = pyPkgs.buildPythonPackage rec {
          pname = "pyflame";
          version = "0.3.1";
          doCheck = false;

          src = pyPkgs.fetchPypi {
            inherit version;
            inherit pname;
            hash = "sha256-1NcQqRe/EnVGdeBY+20Hw3bKUoMaEfj404s0JsXwY0g=";
          };
        };

      in rec {
        devShell = pkgs.mkShell {
          buildInputs = (with pkgs; [ autoflake flamegraph ruff ])
            ++ (with pyPkgs; [
              black
              flake8
              pip
              mypy
              pyflame
              pytest
              jupyter
              sympy
              typing-extensions
              pyeda
            ]) ++ [ logic1 ];
          shellHook = ''
            pip show logic1 pyeda sympy | grep -E 'Name|Version|Summary|Req|---'
            export PYTHONPATH=..:$PYTHONPATH
          '';
	  IPYTHONDIR = "./.ipython";
        };
      });
}
