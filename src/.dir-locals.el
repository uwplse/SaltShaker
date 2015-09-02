((coq-mode . ((eval . (set (make-local-variable 'coq-prog-args)
                             (list 
                               "-emacs-U" 
                               "-I" "/CPUmodels/x86model/Model"
			                   "-I" (expand-file-name "build"
                                 (file-name-directory
                                   (let ((d (dir-locals-find-file ".")))
                                     (if (stringp d) d (car d))))) 
                              ))))))
