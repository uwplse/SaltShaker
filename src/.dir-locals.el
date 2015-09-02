((coq-mode . ((eval . (set (make-local-variable 'coq-prog-args)
                             (list "-emacs-U" "-R"
                               (expand-file-name
                                 "../CPUmodels/x86model/Model"
                                   (file-name-directory
                                     (let ((d (dir-locals-find-file ".")))
                                       (if (stringp d) d (car d)))))
                               ""))))))
