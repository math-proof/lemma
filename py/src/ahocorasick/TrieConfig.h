class TrieConfig {

    bool allowOverlaps = true;

    bool onlyWholeWords = false;

    bool caseInsensitive = false;
public :
    bool isAllowOverlaps() {
        return allowOverlaps;
    }

    void setAllowOverlaps(bool allowOverlaps) {
        this->allowOverlaps = allowOverlaps;
    }

    bool isOnlyWholeWords() {
        return onlyWholeWords;
    }

    void setOnlyWholeWords(bool onlyWholeWords) {
        this->onlyWholeWords = onlyWholeWords;
    }

    bool isCaseInsensitive() {
        return caseInsensitive;
    }

    void setCaseInsensitive(bool caseInsensitive) {
        this->caseInsensitive = caseInsensitive;
    }
};
