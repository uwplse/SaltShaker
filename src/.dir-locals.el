((coq-mode . ((eval . (set (make-local-variable 'coq-prog-args)
                        (list "-emacs-U" "-R" 
                          (replace-regexp-in-string "^/docker:[^:]+:" ""
                            (expand-file-name 
                              "coq"
                                (file-name-directory
                                  (let ((d (dir-locals-find-file ".")))
                                    (if (stringp d) d (car d))))))
                            "Main" "-I" "/CPUmodels/x86model/Model"))))))

