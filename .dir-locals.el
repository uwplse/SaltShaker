((coq-mode . ((eval .
  (let ((root (replace-regexp-in-string "^/docker:[^:]+:" ""
                  (file-name-directory
                    (let ((d (dir-locals-find-file ".")))
                      (if (stringp d) d (car d)))))))
    (set (make-local-variable 'coq-prog-args) (list
      "-emacs-U" "-R" (expand-file-name "src/coq" root) "Main"
                 "-R" (expand-file-name "lib/CPUmodels/x86model/Model" root) "X86Model"
                 "-R" (expand-file-name "lib/SpaceSearch/src/coq" root) "SpaceSearch")))))))
