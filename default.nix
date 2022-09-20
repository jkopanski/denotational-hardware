{ system ? builtins.currentSystem
}:

(builtins.getFlake (toString ./.)).defaultPackage.${system}
